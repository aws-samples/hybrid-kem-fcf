(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: MIT-0 *)

Require Import FCF.
Require Import FCF.PRF.

Set Implicit Arguments.

Class KeyExchange (
  PrivateKey 
  PublicInit
  PublicResponse 
  SharedSecret : Set
  )
  (PublicResponse_EqDec : EqDec PublicResponse)
  (SharedSecret_EqDec : EqDec SharedSecret) := {

  keyGen : Comp (PrivateKey * PublicInit);
  responseFunc : PublicInit -> Comp (option (SharedSecret * PublicResponse));
}.


Section KeyExchange_IND_CPA.

  Context `{KE : KeyExchange}.

  Variable rndSharedSecret : Comp SharedSecret.

  Variable A : PublicInit -> PublicResponse -> SharedSecret -> Comp bool.

  Definition KeyExchangeCPA_G0 :=
    [sk, P] <-$2 keyGen;
    r <-$ responseFunc P;
    match r with
    | None => ret false
    | Some (k, R) => A P R k
    end.

  Definition KeyExchangeCPA_G1 :=
    [sk, P] <-$2 keyGen;
    r <-$ responseFunc P;
    match r with
    | None => ret false
    | Some (_, R) => 
      k <-$ rndSharedSecret;
      A P R k
    end.

  Definition KeyExchangeCPA_Advantage :=
    | Pr[KeyExchangeCPA_G0] - Pr[KeyExchangeCPA_G1] |.

End KeyExchange_IND_CPA.

Section KeyExchange_OW_CPA.

  Context `{KE : KeyExchange}.
    
  Variable A : PublicInit -> PublicResponse -> Comp SharedSecret.

  Definition KeyExchangeOW_CPA_G :=
    [sk, P] <-$2 keyGen;
    r <-$ responseFunc P;
    match r with
    | None => ret false
    | Some (k, R) => 
      k' <-$ A P R;
      ret (k ?= k')
    end. 
    
  Definition KeyExchangeOW_CPA_Advantage :=
    Pr[KeyExchangeOW_CPA_G].

End KeyExchange_OW_CPA.

(* an alternative definition in which the adversary returns a list, and 
wins if the secret is contained within any element in the list.*)
Section KeyExchange_OW_CPA_List.

  Variable D : Set.
  Hypothesis D_EqDec : EqDec D.

  Context `{KE : KeyExchange}.
  Variable containsSecret : SharedSecret -> D -> bool.
  Variable A : PublicInit -> PublicResponse -> Comp (list D).

  Definition KeyExchangeOW_CPA_List_G :=
    [sk, P] <-$2 keyGen;
    r <-$ responseFunc P;
    match r with
    | None => ret false
    | Some (k, R) => 
      ls <-$ A P R;
      ret (any_dec (containsSecret k) ls)
    end. 

  Definition KeyExchangeOW_CPA_List_Advantage :=
    Pr[KeyExchangeOW_CPA_List_G].

End KeyExchange_OW_CPA_List.