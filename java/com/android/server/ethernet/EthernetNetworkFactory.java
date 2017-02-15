/*
 * Copyright (C) 2014 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.android.server.ethernet;

import android.content.Context;
import android.net.ConnectivityManager;
import android.net.DhcpResults;
import android.net.EthernetManager;
import android.net.IEthernetServiceListener;
import android.net.PppoeManager;
import android.net.InterfaceConfiguration;
import android.net.IpConfiguration;
import android.net.IpConfiguration.IpAssignment;
import android.net.IpConfiguration.ProxySettings;
import android.net.LinkProperties;
import android.net.NetworkAgent;
import android.net.NetworkCapabilities;
import android.net.NetworkFactory;
import android.net.NetworkInfo;
import android.net.NetworkInfo.DetailedState;
import android.net.StaticIpConfiguration;
import android.net.ip.IpManager;
import android.net.ip.IpManager.ProvisioningConfiguration;
import android.net.ip.IpManager.WaitForProvisioningCallback;
import android.net.RouteInfo;
import android.net.LinkAddress;
import android.net.NetworkUtils;

import android.os.Handler;
import android.os.IBinder;
import android.os.INetworkManagementService;
import android.os.Looper;
import android.os.RemoteCallbackList;
import android.os.RemoteException;
import android.os.ServiceManager;
import android.text.TextUtils;
import android.util.Log;
import android.content.Intent;
import android.os.UserHandle;
import android.provider.Settings;

import java.io.FileDescriptor;
import java.io.File;
import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.lang.Exception;
import java.net.Inet4Address;
import java.net.Inet6Address;
import java.net.InetAddress;

import com.android.internal.util.IndentingPrintWriter;
import com.android.server.net.BaseNetworkObserver;

import java.io.FileDescriptor;
import java.io.PrintWriter;


/**
 * Manages connectivity for an Ethernet interface.
 *
 * Ethernet Interfaces may be present at boot time or appear after boot (e.g.,
 * for Ethernet adapters connected over USB). This class currently supports
 * only one interface. When an interface appears on the system (or is present
 * at boot time) this class will start tracking it and bring it up, and will
 * attempt to connect when requested. Any other interfaces that subsequently
 * appear will be ignored until the tracked interface disappears. Only
 * interfaces whose names match the <code>config_ethernet_iface_regex</code>
 * regular expression are tracked.
 *
 * This class reports a static network score of 70 when it is tracking an
 * interface and that interface's link is up, and a score of 0 otherwise.
 *
 * @hide
 */
class EthernetNetworkFactory {
    private static final String NETWORK_TYPE = "Ethernet";
    private static final String TAG = "EthernetNetworkFactory";
    private static final int NETWORK_SCORE = 70;
    private static final boolean DBG = true;

    /** Tracks interface changes. Called from NetworkManagementService. */
    private InterfaceObserver mInterfaceObserver;

    /** For static IP configuration */
    private EthernetManager mEthernetManager;

    private PppoeManager mPppoeManager;

    /** To set link state and configure IP addresses. */
    private INetworkManagementService mNMService;

    /* To communicate with ConnectivityManager */
    private NetworkCapabilities mNetworkCapabilities;
    private NetworkAgent mNetworkAgent;
    private LocalNetworkFactory mFactory;
    private Context mContext;

    /** Product-dependent regular expression of interface names we track. */
    private static String mIfaceMatch = "";

    /** To notify Ethernet status. */
    private final RemoteCallbackList<IEthernetServiceListener> mListeners;

    /** Data members. All accesses to these must be synchronized(this). */
    private static String mIface = "";
    private String mHwAddr;
    private static boolean mLinkUp;
    private NetworkInfo mNetworkInfo;
    private LinkProperties mLinkProperties;
    private IpManager mIpManager;
    private Thread mIpProvisioningThread;

    public int mEthernetCurrentState = EthernetManager.ETHER_STATE_DISCONNECTED;
    private boolean mReconnecting;
    private IpAssignment mConnectMode;

    public String dumpEthCurrentState(int curState) {
        if (curState == EthernetManager.ETHER_STATE_DISCONNECTED)
            return "DISCONNECTED";
        else if (curState == EthernetManager.ETHER_STATE_CONNECTING)
            return "CONNECTING";
        else if (curState == EthernetManager.ETHER_STATE_CONNECTED)
            return "CONNECTED";
        else if (curState == EthernetManager.ETHER_STATE_DISCONNECTING)
            return "DISCONNECTING";
        return "DISCONNECTED";
    }

    private void sendEthernetStateChangedBroadcast(int curState) {
        if (mEthernetCurrentState == curState)
            return;
        Log.d(TAG, "sendEthernetStateChangedBroadcast: curState = " + dumpEthCurrentState(curState));
        mEthernetCurrentState = curState;
        final Intent intent = new Intent(EthernetManager.ETHERNET_STATE_CHANGED_ACTION);
        intent.addFlags(Intent.FLAG_RECEIVER_REGISTERED_ONLY_BEFORE_BOOT);
        intent.putExtra(EthernetManager.EXTRA_ETHERNET_STATE, curState);
        mContext.sendStickyBroadcastAsUser(intent, UserHandle.ALL);
    }

    private String ReadFromFile(File file) {
        if((file != null) && file.exists()) {
            try {
                FileInputStream fin= new FileInputStream(file);
                BufferedReader reader= new BufferedReader(new InputStreamReader(fin));
                String flag = reader.readLine();
                fin.close();
                return flag;
            } catch(Exception e) {
                e.printStackTrace();
            }
        }
        return null;
    }

    EthernetNetworkFactory(RemoteCallbackList<IEthernetServiceListener> listeners) {
        mNetworkInfo = new NetworkInfo(ConnectivityManager.TYPE_ETHERNET, 0, NETWORK_TYPE, "");
        mLinkProperties = new LinkProperties();
        initNetworkCapabilities();
        mListeners = listeners;
    }

    private class LocalNetworkFactory extends NetworkFactory {
        LocalNetworkFactory(String name, Context context, Looper looper) {
            super(looper, context, name, new NetworkCapabilities());
        }

        protected void startNetwork() {
            onRequestNetwork();
        }
        protected void stopNetwork() {
        }
    }

    private void stopIpManagerLocked() {
        if (mIpManager != null) {
            mIpManager.shutdown();
            mIpManager = null;
        }
    }

    private void stopIpProvisioningThreadLocked() {
        stopIpManagerLocked();

        if (mIpProvisioningThread != null) {
            mIpProvisioningThread.interrupt();
            mIpProvisioningThread = null;
        }
    }

    private void infoExitIpProvisioningThread() {
        synchronized(EthernetNetworkFactory.this) {
            mIpProvisioningThread = null;
        }
        if (DBG) {
            Log.d(TAG, String.format("exiting ipProvisioningThread(%s): mNetworkInfo=%s",
                            mIface, mNetworkInfo));
        }		
    }

    /**
     * Updates interface state variables.
     * Called on link state changes or on startup.
     */
    private void updateInterfaceState(String iface, boolean up) {
        if (!mIface.equals(iface)) {
            return;
        }
        if (!mReconnecting)
            Log.d(TAG, "updateInterface: " + iface + " link " + (up ? "up" : "down"));

        if (up && mEthernetCurrentState != EthernetManager.ETHER_STATE_DISCONNECTED) {
            Log.d(TAG, "Already connected or connecting, skip connect");
            return;
        }

        synchronized(this) {
            mLinkUp = up;
            mNetworkInfo.setIsAvailable(up);
            if (!up) {
                sendEthernetStateChangedBroadcast(EthernetManager.ETHER_STATE_DISCONNECTING);
                // Tell the agent we're disconnected. It will call disconnect().
                mNetworkInfo.setDetailedState(DetailedState.DISCONNECTED, null, mHwAddr);
                if (mConnectMode == IpAssignment.PPPOE) {
                    Log.d(TAG, "before pppoe stop");
                    mPppoeManager.stopPppoe();
                    Log.d(TAG, "after pppoe stop");
                }
                stopIpProvisioningThreadLocked();
                sendEthernetStateChangedBroadcast(EthernetManager.ETHER_STATE_DISCONNECTED);
            }
            updateAgent();
            // set our score lower than any network could go
            // so we get dropped.  TODO - just unregister the factory
            // when link goes down.
            mFactory.setScoreFilter(up ? NETWORK_SCORE : -1);
        }
    }

    // first disconnect, then connect
    public void reconnect(String iface) {
        Log.d(TAG, "reconnect:");
        mReconnecting = true;

        if (iface == null)
            iface = mIface;

        Log.d(TAG, "first disconnect");
        updateInterfaceState(iface, false);

        try {
            Thread.sleep(1000);
        } catch (InterruptedException ignore) {
        }

        Log.d(TAG, "then connect");
        updateInterfaceState(iface, true);
        mReconnecting = false;
    }

    public void disconnect(String iface) {
        Log.d(TAG, "disconnect:");
        mReconnecting = true;

        if (iface == null)
            iface = mIface;

        updateInterfaceState(iface, false);
        mReconnecting = false;
    }

    private class InterfaceObserver extends BaseNetworkObserver {
        @Override
        public void interfaceLinkStateChanged(String iface, boolean up) {
            updateInterfaceState(iface, up);
        }

        @Override
        public void interfaceAdded(String iface) {
            Log.d(TAG, "interfaceAdded: " + iface);
            maybeTrackInterface(iface);
        }

        @Override
        public void interfaceRemoved(String iface) {
            Log.d(TAG, "interfaceRemoved: " + iface);
            stopTrackingInterface(iface);
        }
    }

    private void setInterfaceUp(String iface) {
        // Bring up the interface so we get link status indications.
        Log.d(TAG, "setInterfaceUp: " + iface);
        try {
            mNMService.setInterfaceUp(iface);
            String hwAddr = null;
            InterfaceConfiguration config = mNMService.getInterfaceConfig(iface);

            if (config == null) {
                Log.e(TAG, "Null iterface config for " + iface + ". Bailing out.");
                return;
            }

            synchronized (this) {
                if (!isTrackingInterface()) {
                    setInterfaceInfoLocked(iface, config.getHardwareAddress());
                    mNetworkInfo.setIsAvailable(true);
                    mNetworkInfo.setExtraInfo(mHwAddr);
                } else {
                    Log.e(TAG, "Interface unexpectedly changed from " + iface + " to " + mIface);
                    mNMService.setInterfaceDown(iface);
                }
            }
        } catch (RemoteException e) {
            Log.e(TAG, "Error upping interface " + mIface + ": " + e);
        }
    }

    private boolean maybeTrackInterface(String iface) {
        // If we don't already have an interface, and if this interface matches
        // our regex, start tracking it.
        if (!iface.matches(mIfaceMatch) || isTrackingInterface())
            return false;

        Log.d(TAG, "Started tracking interface " + iface);
        setInterfaceUp(iface);
        return true;
    }

    private void stopTrackingInterface(String iface) {
        if (!iface.equals(mIface))
            return;

        Log.d(TAG, "Stopped tracking interface " + iface);
        // TODO: Unify this codepath with stop().
        synchronized (this) {
            stopIpProvisioningThreadLocked();
            setInterfaceInfoLocked("", null);
            mNetworkInfo.setExtraInfo(null);
            mLinkUp = false;
            mNetworkInfo.setDetailedState(DetailedState.DISCONNECTED, null, mHwAddr);
            updateAgent();
            mNetworkAgent = null;
            mNetworkInfo = new NetworkInfo(ConnectivityManager.TYPE_ETHERNET, 0, NETWORK_TYPE, "");
            mLinkProperties = new LinkProperties();
            sendEthernetStateChangedBroadcast(EthernetManager.ETHER_STATE_DISCONNECTED);
        }
    }

    private boolean setStaticIpAddress(StaticIpConfiguration staticConfig) {
        if (staticConfig.ipAddress != null &&
                staticConfig.gateway != null &&
                staticConfig.dnsServers.size() > 0) {
            try {
                Log.i(TAG, "Applying static IPv4 configuration to " + mIface + ": " + staticConfig);
                InterfaceConfiguration config = mNMService.getInterfaceConfig(mIface);
                config.setLinkAddress(staticConfig.ipAddress);
                mNMService.setInterfaceConfig(mIface, config);
                return true;
            } catch(RemoteException|IllegalStateException e) {
               Log.e(TAG, "Setting static IP address failed: " + e.getMessage());
            }
        } else {
            Log.e(TAG, "Invalid static IP configuration.");
        }
        return false;
    }

    public void updateAgent() {
        synchronized (EthernetNetworkFactory.this) {
            if (mNetworkAgent == null) return;
            if (DBG) {
                Log.i(TAG, "Updating mNetworkAgent with: " +
                      mNetworkCapabilities + ", " +
                      mNetworkInfo + ", " +
                      mLinkProperties);
            }
            mNetworkAgent.sendNetworkCapabilities(mNetworkCapabilities);
            mNetworkAgent.sendNetworkInfo(mNetworkInfo);
            mNetworkAgent.sendLinkProperties(mLinkProperties);
            // never set the network score below 0.
            mNetworkAgent.sendNetworkScore(mLinkUp? NETWORK_SCORE : 0);
        }
    }

    /* Called by the NetworkFactory on the handler thread. */
    public void onRequestNetwork() {
        int carrier = getEthernetCarrierState(mIface);
        Log.d(TAG, "onRequestNetwork: " + mIface + " carrier = " + carrier);
        if (carrier != 1) {
            return;
        }

        synchronized(EthernetNetworkFactory.this) {
            if (mIpProvisioningThread != null) {
                Log.d(TAG, "mIpProvisioningThread is already running");
                return;
            }
        }

        sendEthernetStateChangedBroadcast(EthernetManager.ETHER_STATE_CONNECTING);
        final Thread ipProvisioningThread = new Thread(new Runnable() {
            public void run() {
                if (DBG) {
                    Log.d(TAG, String.format("starting ipProvisioningThread(%s): mNetworkInfo=%s",
                            mIface, mNetworkInfo));
                }

                LinkProperties linkProperties;

                IpConfiguration config = mEthernetManager.getConfiguration();
                mConnectMode = config.getIpAssignment();
                if (mPppoeManager == null) {
                    mConnectMode = IpAssignment.DHCP;
                    Log.d(TAG, "mPppoeManager == null, set mConnectMode to DHCP");
                }
                if (config.getIpAssignment() == IpAssignment.STATIC) {
                    Log.d(TAG, "config STATIC");
                    if (!setStaticIpAddress(config.getStaticIpConfiguration())) {
                        // We've already logged an error.
                        sendEthernetStateChangedBroadcast(EthernetManager.ETHER_STATE_DISCONNECTED);
                        infoExitIpProvisioningThread();
                        return;
                    }
                    linkProperties = config.getStaticIpConfiguration().toLinkProperties(mIface);
                } else if (config.getIpAssignment() == IpAssignment.PPPOE) {
                    Log.d(TAG, "config PPPOE");
                    Log.d(TAG, "start pppoe connect: " + config.pppoeAccount + ", " + config.pppoePassword);
                    mPppoeManager.connect(config.pppoeAccount, config.pppoePassword, mIface);

                    int state = mPppoeManager.getPppoeState();
                    Log.d(TAG, "end pppoe connect: state = " + mPppoeManager.dumpCurrentState(state));
                    if (state == PppoeManager.PPPOE_STATE_CONNECT) {
                        linkProperties = mPppoeManager.getLinkProperties();
                        String iface = mPppoeManager.getPppIfaceName();
                        /*Log.d(TAG, "addInterfaceToLocalNetwork: iface = " + iface + ", route = " + linkProperties.getRoutes()); 
                        try {
                            mNMService.addInterfaceToLocalNetwork(iface, linkProperties.getRoutes());
                        } catch (RemoteException e) {
                            Log.e(TAG, "Failed to add iface " + iface + " to local network " + e);
                        }*/
                        linkProperties.setInterfaceName(iface);
                    } else {
                        Log.e(TAG, "pppoe connect failed.");
                        //mFactory.setScoreFilter(-1);
                        sendEthernetStateChangedBroadcast(EthernetManager.ETHER_STATE_DISCONNECTED);
                        infoExitIpProvisioningThread();
                        return;
                    }
                } else {
                    Log.d(TAG, "config DHCP");
                    mNetworkInfo.setDetailedState(DetailedState.OBTAINING_IPADDR, null, mHwAddr);
                    WaitForProvisioningCallback ipmCallback = new WaitForProvisioningCallback() {
                        @Override
                        public void onLinkPropertiesChange(LinkProperties newLp) {
                            Log.d(TAG, "onLinkPropertiesChange: lp = " + newLp);
                            synchronized(EthernetNetworkFactory.this) {
                                if (mNetworkAgent != null && mNetworkInfo.isConnected()) {
                                    mLinkProperties = newLp;
                                    mNetworkAgent.sendLinkProperties(newLp);
                                }
                            }
                        }
                    };

                    synchronized(EthernetNetworkFactory.this) {
                        stopIpManagerLocked();
                        if (!isTrackingInterface()) {
                            sendEthernetStateChangedBroadcast(EthernetManager.ETHER_STATE_DISCONNECTED);
                            infoExitIpProvisioningThread();
                            return;
                        }

                        mIpManager = new IpManager(mContext, mIface, ipmCallback);

                        if (config.getProxySettings() == ProxySettings.STATIC ||
                                config.getProxySettings() == ProxySettings.PAC) {
                            mIpManager.setHttpProxy(config.getHttpProxy());
                        }

                        final String tcpBufferSizes = mContext.getResources().getString(
                                com.android.internal.R.string.config_ethernet_tcp_buffers);
                        if (!TextUtils.isEmpty(tcpBufferSizes)) {
                            mIpManager.setTcpBufferSizes(tcpBufferSizes);
                        }

                        final ProvisioningConfiguration provisioningConfiguration =
                                mIpManager.buildProvisioningConfiguration()
                                        .withProvisioningTimeoutMs(0)
                                        .build();
                        mIpManager.startProvisioning(provisioningConfiguration);
                    }

                    linkProperties = ipmCallback.waitForProvisioning();
                    if (linkProperties == null) {
                        Log.e(TAG, "IP provisioning error");
                        // set our score lower than any network could go
                        // so we get dropped.
                        mFactory.setScoreFilter(-1);
                        synchronized(EthernetNetworkFactory.this) {
                            stopIpManagerLocked();
                        }
                        sendEthernetStateChangedBroadcast(EthernetManager.ETHER_STATE_DISCONNECTED);
                        infoExitIpProvisioningThread();					
                        return;
                    }
                }

                synchronized(EthernetNetworkFactory.this) {
                    if (mNetworkAgent != null) {
                        Log.e(TAG, "Already have a NetworkAgent - aborting new request");
                        stopIpManagerLocked();
                        infoExitIpProvisioningThread();
                        return;
                    }
                    Log.d(TAG, "success get ip: lp = " + linkProperties);
                    mLinkProperties = linkProperties;
                    mNetworkInfo.setIsAvailable(true);
                    mNetworkInfo.setDetailedState(DetailedState.CONNECTED, null, mHwAddr);
                    sendEthernetStateChangedBroadcast(EthernetManager.ETHER_STATE_CONNECTED);

                    // Create our NetworkAgent.
                    mNetworkAgent = new NetworkAgent(mFactory.getLooper(), mContext,
                            NETWORK_TYPE, mNetworkInfo, mNetworkCapabilities, mLinkProperties,
                            NETWORK_SCORE) {
                        public void unwanted() {
                            synchronized(EthernetNetworkFactory.this) {
                                if (this == mNetworkAgent) {
                                    Log.d(TAG, "unwanted");
                                    stopIpManagerLocked();

                                    mLinkProperties.clear();
                                    mNetworkInfo.setDetailedState(DetailedState.DISCONNECTED, null,
                                            mHwAddr);
                                    updateAgent();
                                    mNetworkAgent = null;
                                    try {
                                        mNMService.clearInterfaceAddresses(mIface);
                                    } catch (Exception e) {
                                        Log.e(TAG, "Failed to clear addresses or disable ipv6" + e);
                                    }
                                    sendEthernetStateChangedBroadcast(EthernetManager.ETHER_STATE_DISCONNECTED);
                                } else {
                                    Log.d(TAG, "Ignoring unwanted as we have a more modern " +
                                            "instance");
                                }
                            }
                        };
                    };
                }

                infoExitIpProvisioningThread();
            }
        });

        synchronized(EthernetNetworkFactory.this) {
            if (mIpProvisioningThread == null) {
                mIpProvisioningThread = ipProvisioningThread;
                mIpProvisioningThread.start();
            }
        }
    }

    /**
     * Begin monitoring connectivity
     */
    public synchronized void start(Context context, Handler target) {
        // The services we use.
        IBinder b = ServiceManager.getService(Context.NETWORKMANAGEMENT_SERVICE);
        mNMService = INetworkManagementService.Stub.asInterface(b);
        mEthernetManager = (EthernetManager) context.getSystemService(Context.ETHERNET_SERVICE);
        mPppoeManager = (PppoeManager) context.getSystemService(Context.PPPOE_SERVICE);

        // Interface match regex.
        mIfaceMatch = context.getResources().getString(
                com.android.internal.R.string.config_ethernet_iface_regex);
        Log.d(TAG, "EthernetNetworkFactory start " + mIfaceMatch);

        // Create and register our NetworkFactory.
        mFactory = new LocalNetworkFactory(NETWORK_TYPE, context, target.getLooper());
        mFactory.setCapabilityFilter(mNetworkCapabilities);
        mFactory.setScoreFilter(-1); // this set high when we have an iface
        mFactory.register();

        mContext = context;
        mReconnecting = false;
        mConnectMode = IpAssignment.DHCP;

        // Start tracking interface change events.
        mInterfaceObserver = new InterfaceObserver();
        try {
            mNMService.registerObserver(mInterfaceObserver);
        } catch (RemoteException e) {
            Log.e(TAG, "Could not register InterfaceObserver " + e);
        }

        // If an Ethernet interface is already connected, start tracking that.
        // Otherwise, the first Ethernet interface to appear will be tracked.
        try {
            final String[] ifaces = mNMService.listInterfaces();
            for (String iface : ifaces) {
                synchronized(this) {
                    if (maybeTrackInterface(iface)) {
                        // We have our interface. Track it.
                        // Note: if the interface already has link (e.g., if we
                        // crashed and got restarted while it was running),
                        // we need to fake a link up notification so we start
                        // configuring it. Since we're already holding the lock,
                        // any real link up/down notification will only arrive
                        // after we've done this.
                        //if (mNMService.getInterfaceConfig(iface).hasFlag("running")) {
                        new Thread(new Runnable() {
                            public void run() {
                                // carrier is always 1 when kernel boot up no matter RJ45 plugin or not, 
                                // sleep a little time to wait kernel's correct carrier status
                                try {
                                    Thread.sleep(3000);
                                } catch (InterruptedException ignore) {
                                }
                                int carrier = getEthernetCarrierState(iface);
                                Log.d(TAG, iface + " carrier = " + carrier);
                                if (carrier == 1) {
                                    updateInterfaceState(iface, true);
                                }
                            }
                        }).start();
                        break;
                    }
                }
            }
        } catch (RemoteException|IllegalStateException e) {
            Log.e(TAG, "Could not get list of interfaces " + e);
        }
    }

    public synchronized void stop() {
        Log.d(TAG, "EthernetNetworkFactory stop");
        stopIpProvisioningThreadLocked();
        // ConnectivityService will only forget our NetworkAgent if we send it a NetworkInfo object
        // with a state of DISCONNECTED or SUSPENDED. So we can't simply clear our NetworkInfo here:
        // that sets the state to IDLE, and ConnectivityService will still think we're connected.
        //
        // TODO: stop using explicit comparisons to DISCONNECTED / SUSPENDED in ConnectivityService,
        // and instead use isConnectedOrConnecting().
        mNetworkInfo.setDetailedState(DetailedState.DISCONNECTED, null, mHwAddr);
        mLinkUp = false;
        updateAgent();
        mLinkProperties = new LinkProperties();
        mNetworkAgent = null;
        setInterfaceInfoLocked("", null);
        mNetworkInfo = new NetworkInfo(ConnectivityManager.TYPE_ETHERNET, 0, NETWORK_TYPE, "");
        mFactory.unregister();
        sendEthernetStateChangedBroadcast(EthernetManager.ETHER_STATE_DISCONNECTED);
    }

    private void initNetworkCapabilities() {
        mNetworkCapabilities = new NetworkCapabilities();
        mNetworkCapabilities.addTransportType(NetworkCapabilities.TRANSPORT_ETHERNET);
        mNetworkCapabilities.addCapability(NetworkCapabilities.NET_CAPABILITY_INTERNET);
        mNetworkCapabilities.addCapability(NetworkCapabilities.NET_CAPABILITY_NOT_RESTRICTED);
        // We have no useful data on bandwidth. Say 100M up and 100M down. :-(
        mNetworkCapabilities.setLinkUpstreamBandwidthKbps(100 * 1000);
        mNetworkCapabilities.setLinkDownstreamBandwidthKbps(100 * 1000);
    }

    public synchronized boolean isTrackingInterface() {
        return !TextUtils.isEmpty(mIface);
    }

    public int getEthernetCarrierState(String ifname) {
        if(ifname != "") {
            try {
                File file = new File("/sys/class/net/" + ifname + "/carrier");
                String carrier = ReadFromFile(file);
                return Integer.parseInt(carrier);
            } catch(Exception e) {
                e.printStackTrace();
                return 0;
            }
        } else {
            return 0;
        }
    }

    public String getEthernetMacAddress(String ifname) {
        if(ifname != "") {
            try {
                File file = new File("/sys/class/net/" + ifname + "/address");
                String address = ReadFromFile(file);
                return address;
            } catch(Exception e) {
                e.printStackTrace();
                return "";
            }
        } else {
            return "";
        }
    }

    public String getIpAddress() {
        IpConfiguration config = mEthernetManager.getConfiguration();
        if (config.getIpAssignment() == IpAssignment.STATIC) {
            return config.getStaticIpConfiguration().ipAddress.getAddress().getHostAddress();
        } else {
            for (LinkAddress l : mLinkProperties.getLinkAddresses()) {
                InetAddress source = l.getAddress();
                //Log.d(TAG, "getIpAddress: " + source.getHostAddress());
                if (source instanceof Inet4Address) {
                    return source.getHostAddress();
                }
            }
        }
        return "";
    }

    private String prefix2netmask(int prefix) {
        // convert prefix to netmask
        if (true) {
            int mask = 0xFFFFFFFF << (32 - prefix);
            //Log.d(TAG, "mask = " + mask + " prefix = " + prefix);
            return ((mask>>>24) & 0xff) + "." + ((mask>>>16) & 0xff) + "." + ((mask>>>8) & 0xff) + "." + ((mask) & 0xff);
    	   } else {
    	       return NetworkUtils.intToInetAddress(NetworkUtils.prefixLengthToNetmaskInt(prefix)).getHostName();
    	   }
    }

    public String getNetmask() {
        IpConfiguration config = mEthernetManager.getConfiguration();
        if (config.getIpAssignment() == IpAssignment.STATIC) {
            return prefix2netmask(config.getStaticIpConfiguration().ipAddress.getPrefixLength());
        } else {
            for (LinkAddress l : mLinkProperties.getLinkAddresses()) {
                InetAddress source = l.getAddress();
                if (source instanceof Inet4Address) {
                    return prefix2netmask(l.getPrefixLength());
                }
            }
        }
        return "";
    }
	
    public String getGateway() {
        IpConfiguration config = mEthernetManager.getConfiguration();
        if (config.getIpAssignment() == IpAssignment.STATIC) {
            return config.getStaticIpConfiguration().gateway.getHostAddress();
        } else {
            for (RouteInfo route : mLinkProperties.getRoutes()) {
                if (route.hasGateway()) {
                    InetAddress gateway = route.getGateway();
                    if (route.isIPv4Default()) {
                        return gateway.getHostAddress();
                    }
                }
            }
        }
        return "";		
    }

    /*
     * return dns format: "8.8.8.8,4.4.4.4"
     */
    public String getDns() {
        String dns = "";
        IpConfiguration config = mEthernetManager.getConfiguration();
        if (config.getIpAssignment() == IpAssignment.STATIC) {
            for (InetAddress nameserver : config.getStaticIpConfiguration().dnsServers) {
                dns += nameserver.getHostAddress() + ",";
            }			
        } else {		
            for (InetAddress nameserver : mLinkProperties.getDnsServers()) {
                dns += nameserver.getHostAddress() + ",";
            }
        }
        return dns;		
    }

    /**
     * Set interface information and notify listeners if availability is changed.
     * This should be called with the lock held.
     */
    private void setInterfaceInfoLocked(String iface, String hwAddr) {
        boolean oldAvailable = isTrackingInterface();
        mIface = iface;
        mHwAddr = hwAddr;
        boolean available = isTrackingInterface();

        if (oldAvailable != available) {
            int n = mListeners.beginBroadcast();
            for (int i = 0; i < n; i++) {
                try {
                    mListeners.getBroadcastItem(i).onAvailabilityChanged(available);
                } catch (RemoteException e) {
                    // Do nothing here.
                }
            }
            mListeners.finishBroadcast();
        }
    }

    synchronized void dump(FileDescriptor fd, IndentingPrintWriter pw, String[] args) {
        if (isTrackingInterface()) {
            pw.println("Tracking interface: " + mIface);
            pw.increaseIndent();
            pw.println("MAC address: " + mHwAddr);
            pw.println("Link state: " + (mLinkUp ? "up" : "down"));
            pw.decreaseIndent();
        } else {
            pw.println("Not tracking any interface");
        }

        pw.println();
        pw.println("mEthernetCurrentState: " + dumpEthCurrentState(mEthernetCurrentState));

        pw.println();
        pw.println("NetworkInfo: " + mNetworkInfo);
        pw.println("LinkProperties: " + mLinkProperties);
        pw.println("NetworkAgent: " + mNetworkAgent);
        if (mIpManager != null) {
            pw.println("IpManager:");
            pw.increaseIndent();
            mIpManager.dump(fd, pw, args);
            pw.decreaseIndent();
        }
    }
}
