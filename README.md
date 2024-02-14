# stateful_snat_dpdk

Based on DPDK Sample l2fwd and [Stateful-NAT-using-DPDK](https://github.com/codelearner3012/Stateful-NAT-using-DPDK) by codelearner3012 

DPDK version: 22.11.1

Readme given by codelearner3012 (To be edited later)

DPDK 
The Data Plane Development Kit provides a framework for processing packets in the userspace. The NIC is a device from which the incoming packets are read into the Rx and Tx queues where they are passed onto the network stack which also lies in the kernel. DPDK allows accessing and re-writing of the different layers (Ethernet, IP, or TCP/UDP) packet headers in the userspace. In order to maintain the performance efficiency of the application built using DPDK, the development kit provides a poll-mode driver which polls the ethernet driver buffers and reads the packets from the ring buffers onto the user allocated mbufs. To further optimize the runtime performance huge page tables are allocated containing pointers to the packets read onto the mbuf. Tying this all together, it provides a rich Environment Abstraction Layer which pre-allocates memory and creates threads for queues associated with the different ports. These threads receiving and sending packets are distributed across the different cores based on CPU set availability and they then maintain an affinity to the cores. Using the DPDK environment instead of other lightweight mechanisms such as eBPF is mainly the inability to modify packet data and a high learning curve associated with writing custom filter rules to be passed to the kernel. Even though there are available APIs a lot of them embed assembly code making it difficult to interface with. 

Stateful source-NAT
Stateful NAT Application A stateful NAT application replaces the source IP belonging to a private network to a public IP address which is then routed through the internet. In large scale application deployments over the cloud, a single application may span multiple data centers and need to rely on the routers available at the cloud service provider to route the packet through the network. Further, the application may have created an overlay network using a set of private IP addresses across the data centers requiring a customized NAT application to facilitate communication between the required areas.
