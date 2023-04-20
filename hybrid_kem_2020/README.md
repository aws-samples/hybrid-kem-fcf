## Mechanized Security Proofs for Hybrid Key Encapsulation using Concatenating and Cascading Combiners

This project contains mechanized cryptographic security proofs for two simple hybrid Key Encapsulation Mechanisms (KEMs). 

## Source Files and Proofs

* KeyExchange.v---Security definitions for KEMs in the standard model.
* KeyExchange_ROM.v---Security definitions for KEMs in the random oracle model.
* HybridKE_ROM.v---Proof of IND-CPA security of the concatenation KEM in the random oracle model.
* HybridKE.v---Proof of IND-CPA security of the concatenation KEM in the standard model.
* HybridKE_Cascade_ROM.v---Proof of IND-CPA security of the cascade KEM in the standard model.


## License

This library is licensed under the MIT-0 License. See the LICENSE file.

