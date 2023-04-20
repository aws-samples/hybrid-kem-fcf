## Mechanized Security Proofs for Hybrid Key Encapsulation

This repository contains mechanized cryptographic security proofs for two simple hybrid Key Encapsulation Mechanisms (KEMs). 

## Organization

This repository contains multiple projects containing proofs of different hybrid KEMs using different assumptions and models. The projects are listed below. View the README file in each project directory to get more information.

Projects:
* hybrid_kem_2020: Proofs of IND-CPA security of hybrid KEMs based on concatenating and cascading combiners. 
* ctkdf_2023: Proofs of IND-CPA and IND-CCA security of a hybrid KEM based on a concatenating combiner.

## Building

Checking this proof requires:
* [Coq](https://coq.inria.fr/). The proof has been tested with Coq version 8.17. 
* [FCF](https://github.com/adampetcher/fcf). The Makefile and other settings for this proof looks for FCF in a parallel directory. Specifically, the directory structure should look like:
  * HybridKE_FCF
    * README.md
    * hybrid_kem_2020
    * ctkdf_2023
    * (etc.)
  * FCF
    * src
    * Makefile
    * (etc.)

To build, first run `make` in the FCF directory. Then change to the desired project directory and run `make`.


## License

This library is licensed under the MIT-0 License. See the LICENSE file.

