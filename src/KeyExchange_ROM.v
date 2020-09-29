(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: MIT-0 *)

Require Import FCF.
Require Import FCF.PRF.
Require Import FCF.ROM.

Set Implicit Arguments.

Class KeyExchange_ROM (
  PrivateKey 
  PublicInit
  PublicResponse 
  SharedSecret 
  DomainRO RangeRO : Set
  )
  (PublicResponse_EqDec : EqDec PublicResponse)
  (SharedSecret_EqDec : EqDec SharedSecret) := {

  keyGen_ROM : OracleComp DomainRO RangeRO (PrivateKey * PublicInit);
  responseFunc_ROM : PublicInit -> OracleComp DomainRO RangeRO (option (SharedSecret * PublicResponse));
  
}.

Section KeyExchange_IND_CPA_ROM.

  Context `{KE : KeyExchange_ROM}.

  Variable rndSharedSecret : Comp SharedSecret.

  Variable A : PublicInit -> PublicResponse -> SharedSecret -> OracleComp DomainRO RangeRO bool. 

  Hypothesis DomainRO_EqDec : EqDec DomainRO.
  Hypothesis RangeRO_EqDec : EqDec RangeRO.
  Variable rndRange : Comp RangeRO.

  Definition KeyExchangeCPA_ROM_G0 :=
    [sk, P] <--$2 keyGen_ROM;
    r <--$ responseFunc_ROM P;
    match r with
    | None => $ret false
    | Some (k, R) =>
      (A P R k)
    end.

  Definition KeyExchangeCPA_ROM_G1 :=
    [sk, P] <--$2 keyGen_ROM;
    r <--$ responseFunc_ROM P;
    match r with
    | None => $ret false
    | Some (_, R) =>
      k <--$$ rndSharedSecret;
      (A P R k)
    end.


  Definition KeyExchangeCPA_O_Advantage :=
    | Pr[ExpROM _ _ rndRange _ KeyExchangeCPA_ROM_G0] - Pr[ExpROM _ _ rndRange _ KeyExchangeCPA_ROM_G1] |.

End KeyExchange_IND_CPA_ROM.
