# DMA Architecture References

Published precedents for architectural ideas used in the DMA family. These citations record convergence with earlier work; they do not imply that the RTL was derived from these sources.

Local PDFs use the `<Topic>__<FirstAuthor><Year>.pdf` naming convention. Entries without a local PDF retain a full citation and an authoritative DOI or source link.

## Flow control and buffer reservation

- Li-Shiuan Peh and William J. Dally, "Flit-Reservation Flow Control," *Proceedings of the Sixth International Symposium on High-Performance Computer Architecture (HPCA)*, 2000, pp. 73-84. DOI: [10.1109/HPCA.2000.824340](https://doi.org/10.1109/HPCA.2000.824340). [Author-hosted PDF](https://cva.stanford.edu/publications/1999/flit_rsvn.pdf). Supports reserving buffer space and bandwidth ahead of data arrival.
- H. T. Kung, Trevor Blackwell, and Alan Chapman, "Credit-Based Flow Control for ATM Networks: Credit Update Protocol, Adaptive Credit Allocation, and Statistical Multiplexing," *Proceedings of ACM SIGCOMM 1994*, pp. 101-114. DOI: [10.1145/190314.190324](https://doi.org/10.1145/190314.190324). [Author-hosted PDF](https://www.eecs.harvard.edu/~htk/publication/1994-sigcomm-kung-blackwell-chapman.pdf). Supports credit accounting, in-flight subtraction, per-flow buffer allocation, and bandwidth-delay credit sizing.

## Decoupling, prefetching, and latency tolerance

- James E. Smith, "Decoupled Access/Execute Computer Architectures," *ACM Transactions on Computer Systems* 2(4), November 1984, pp. 289-308. DOI: [10.1145/357401.357403](https://doi.org/10.1145/357401.357403). Supports autonomous producers and consumers connected by queues.
- Tao Chen and G. Edward Suh, "Efficient Data Supply for Hardware Accelerators with Prefetching and Access/Execute Decoupling," *Proceedings of the 49th Annual IEEE/ACM International Symposium on Microarchitecture (MICRO)*, 2016. DOI: [10.1109/MICRO.2016.7783749](https://doi.org/10.1109/MICRO.2016.7783749). [Authoritative abstract and publication links](https://www.csl.cornell.edu/~tchen/abstract/accelmem-micro16/). Supports prefetching and access/execute decoupling for variable memory latency.
- Luca P. Carloni, Kenneth L. McMillan, and Alberto L. Sangiovanni-Vincentelli, "Theory of Latency-Insensitive Design," *IEEE Transactions on Computer-Aided Design of Integrated Circuits and Systems* 20(9), September 2001, pp. 1059-1076. DOI: [10.1109/43.945302](https://doi.org/10.1109/43.945302). [Author-hosted PDF](http://webcluster.cs.columbia.edu/~luca/research/lipTransactions.pdf). Supports stallable modules, backpressure, and latency bridging.

## Outstanding transactions and bandwidth-delay limits

- Daniel Lenoski et al., "The DASH Prototype: Implementation and Performance," *Proceedings of the 19th Annual International Symposium on Computer Architecture (ISCA)*, 1992, pp. 92-103. DOI: [10.1145/146628.139706](https://doi.org/10.1145/146628.139706). Supports tagged split transactions with requests and responses independently outstanding.
- John D. C. Little, "A Proof for the Queuing Formula: L = λW," *Operations Research* 9(3), May-June 1961, pp. 383-387. DOI: [10.1287/opre.9.3.383](https://doi.org/10.1287/opre.9.3.383). [Course-hosted PDF](https://www2.isye.gatech.edu/~spyros/courses/IE7201/Fall-13/Little-OR-paper.pdf). Supports the relationship among in-flight work, throughput, and latency.

## Commercial DMA comparison

- AMD/Xilinx, *AXI MCDMA Product Guide PG288*, 2017. [Official product guide](https://docs.amd.com/api/khub/documents/pYERDdVbLWxnOwYMeCp9_Q/content). Provides a comparison for multiple channels, per-channel descriptor queues, independent descriptor fetching and data movement, and independent MM2S and S2MM paths.
