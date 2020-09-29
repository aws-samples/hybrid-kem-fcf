## Mechanized Security Proofs for Hybrid Key Encapsulation

This repository contains mechanized cryptographic security proofs for two simple hybrid Key Encapsulation Mechanisms (KEMs). 

## Building

Checking this proof requires:
* [Coq](https://coq.inria.fr/). The proof has been tested with Coq version 8.9, but any recent version is expected to work. 
* [FCF](https://github.com/adampetcher/fcf). The Makefile and other settings for this proof looks for FCF in a parallel directory. Specifically, the directory structure should look like:
  * HybridKE_FCF
    * src
    * Makefile
    * (etc.)
  * FCF
    * src
    * Makefile
    * (etc.)

To build, run "make" in the FCF directory and then "make" in this project's directory.

## Source Files and Proofs

* KeyExchange.v---Security definitions for KEMs in the standard model.
* KeyExchange_ROM.v---Security definitions for KEMs in the random oracle model.
* HybridKE_ROM.v---Proof of IND-CPA security of the concatenation KEM in the random oracle model.
* HybridKE.v---Proof of IND-CPA security of the concatenation KEM in the standard model.
* HybridKE_Cascade_ROM.v---Proof of IND-CPA security of the cascade KEM in the standard model.


## License

This library is licensed under the MIT-0 License. See the LICENSE file.

