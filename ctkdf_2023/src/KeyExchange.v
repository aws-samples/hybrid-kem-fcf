(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: MIT-0 *)

Require Import FCF.
Require Import FCF.PRF.

Set Implicit Arguments.


Class KeyExchange (
  PrivateKey 
  PublicInit
  PublicResponse 
  Aux
  SharedSecret : Set
  )
  (PublicResponse_EqDec : EqDec PublicResponse)
  (SharedSecret_EqDec : EqDec SharedSecret) := {

  keyGen : Comp (PrivateKey * PublicInit);
  responseFunc : PublicInit -> Comp (option (SharedSecret * PublicResponse * Aux));
  decapsFunc : PrivateKey -> PublicResponse -> Comp (option SharedSecret);
}.


Section KeyExchange_Correct.
  Context `{KE : KeyExchange}.

  Definition KE_Correctness_G :=
    [pri, pub] <-$2 keyGen;
    r_opt <-$ responseFunc pub;
    match r_opt with
    | None => ret false
    | Some (s1, resp, _) => 
      s2 <-$ decapsFunc pri resp;
      ret (negb (eqb (Some s1) s2))
    end.

  Definition KE_CorrectnessError :=
    Pr[KE_Correctness_G].

End KeyExchange_Correct.
  

Section KeyExchange_IND_CPA.

  Context `{KE : KeyExchange}.

  Variable rndSharedSecret : Comp SharedSecret.

  Variable A : PublicInit -> PublicResponse -> SharedSecret -> Aux -> Comp bool.

  Definition KeyExchangeCPA_G0 :=
    [sk, P] <-$2 keyGen;
    r_opt <-$ responseFunc P;
    match r_opt with
    | None => ret false
    | Some (k, R, a) => 
      A P R k a
    end.

  Definition KeyExchangeCPA_G1 :=
    [sk, P] <-$2 keyGen;
    r_opt <-$ responseFunc P;
    match r_opt with
    | None => ret false
    | Some (_, R, a) => 
      k <-$ rndSharedSecret;
      A P R k a
    end.

  Definition KeyExchangeCPA_Advantage :=
    | Pr[KeyExchangeCPA_G0] - Pr[KeyExchangeCPA_G1] |.

End KeyExchange_IND_CPA.

Section KeyExchange_OW_CCA_List.

  Context `{KE : KeyExchange}.
  Variable A : PublicInit -> PublicResponse -> Aux -> OracleComp PublicResponse (option SharedSecret) (list SharedSecret).

  Definition ccaOracle R sk (_ : unit) R' := 
    (if (R' ?= R) then (ret (None, tt)) else x <-$ decapsFunc sk R'; ret (x, tt)).

  Definition KeyExchangeOW_CCA_List_G :=
    [sk, P] <-$2 keyGen;
    r_opt <-$ responseFunc P;
    match r_opt with
    | None => ret false
    | Some (k, R, a) => 
      [ls, _] <-$2 (A P R a) _ _ (ccaOracle R sk) tt;
      ret (any_dec (eqb k) ls)
    end.

  Definition KeyExchangeOW_CCA_List_Advantage :=
    Pr[KeyExchangeOW_CCA_List_G].

End KeyExchange_OW_CCA_List.

Require Import FCF.ROM.

Set Implicit Arguments.

Class KeyExchange_ROM (
  PrivateKey 
  PublicInit
  PublicResponse 
  SharedSecret 
  Aux
  DomainRO RangeRO : Set
  )
  (PublicResponse_EqDec : EqDec PublicResponse)
  (SharedSecret_EqDec : EqDec SharedSecret) := {

  keyGen_ROM : OracleComp DomainRO RangeRO (PrivateKey * PublicInit);
  responseFunc_ROM : PublicInit -> OracleComp DomainRO RangeRO (option (SharedSecret * PublicResponse * Aux));
  decapsFunc_ROM : PrivateKey -> PublicResponse -> OracleComp DomainRO RangeRO (option SharedSecret);
}.
  

Section KeyExchange_IND_CPA_ROM.

  Context `{KE : KeyExchange_ROM}.

  Variable rndSharedSecret : Comp SharedSecret.

  Variable A : PublicInit -> PublicResponse -> SharedSecret -> Aux -> OracleComp DomainRO RangeRO bool. 

  Hypothesis DomainRO_EqDec : EqDec DomainRO.
  Hypothesis RangeRO_EqDec : EqDec RangeRO.
  Variable rndRange : Comp RangeRO.

  Definition KeyExchangeCPA_ROM_G0 :=
    [sk, P] <--$2 keyGen_ROM;
    r_opt <--$ responseFunc_ROM P;
    match r_opt with
    | None => $ret false
    | Some (k, R, a) =>
      (A P R k a)
    end.

  Definition KeyExchangeCPA_ROM_G1 :=
    [sk, P] <--$2 keyGen_ROM;
    r_opt <--$ responseFunc_ROM P;
    match r_opt with
    | None => $ret false
    | Some (_, R, a) =>
      k <--$$ rndSharedSecret;
      (A P R k a)
    end.

  Definition KeyExchangeCPA_O_Advantage :=
    | Pr[ExpROM _ _ rndRange _ KeyExchangeCPA_ROM_G0] - Pr[ExpROM _ _ rndRange _ KeyExchangeCPA_ROM_G1] |.

End KeyExchange_IND_CPA_ROM.

Section KeyExchange_CCA_ROM.

  Context `{KE : KeyExchange_ROM}.

  Hypothesis DomainRO_EqDec : EqDec DomainRO.
  Hypothesis RangeRO_EqDec : EqDec RangeRO.

  Inductive CCA_OracleQuery :=
  | cca_oq_ro : DomainRO -> CCA_OracleQuery
  | cca_oq_dec : PublicResponse -> CCA_OracleQuery.

  Inductive CCA_OracleResponse :=
  | cca_or_ro : RangeRO -> CCA_OracleResponse
  | cca_or_dec : (option SharedSecret) -> CCA_OracleResponse.

  Definition eqb_CCA_OracleQuery (q1 q2 : CCA_OracleQuery) :=
    match q1 with
    | cca_oq_ro d1 =>
      match q2 with
      | cca_oq_ro d2 => eqb d1 d2
      | cca_oq_dec _ => false
      end
    | cca_oq_dec r1 =>
      match q2 with
      | cca_oq_ro _ => false
      | cca_oq_dec r2 =>
        eqb r1 r2
      end
    end.

  Theorem eqb_CCA_OracleQuery_leibniz : forall q1 q2,
    (eqb_CCA_OracleQuery q1 q2 = true) <-> q1 = q2.

    intros; unfold eqb_CCA_OracleQuery in *; intuition idtac; subst.
    destruct q1; destruct q2; simpl in *; try discriminate.
    rewrite eqb_leibniz in H; subst; reflexivity.
    rewrite eqb_leibniz in H; subst; reflexivity.
      
    destruct q2; simpl in *; apply eqb_refl.

  Qed.

  Instance CCA_OracleQuery_EqDec : EqDec CCA_OracleQuery.

    apply (Build_EqDec eqb_CCA_OracleQuery eqb_CCA_OracleQuery_leibniz).
  Qed.

  Definition eqb_CCA_OracleResponse (r1 r2 : CCA_OracleResponse) :=
    match r1 with
    | cca_or_ro r1 =>
      match r2 with
      | cca_or_ro r2 => eqb r1 r2
      | cca_or_dec _ => false
      end
    | cca_or_dec s1 =>
      match r2 with
      | cca_or_ro _ => false
      | cca_or_dec s2 =>
        eqb s1 s2
      end
    end.

  Theorem eqb_CCA_OracleResponse_leibniz : forall q1 q2,
    (eqb_CCA_OracleResponse q1 q2 = true) <-> q1 = q2.

    intros; unfold eqb_CCA_OracleResponse in *; intuition idtac; subst.
    destruct q1; destruct q2; simpl in *; try discriminate.
    rewrite eqb_leibniz in H; subst; reflexivity.
    rewrite eqb_leibniz in H; subst; reflexivity.
      
    destruct q2; simpl in *; apply eqb_refl.

  Qed.

  Instance CCA_OracleResponse_EqDec : EqDec CCA_OracleResponse.
    apply (Build_EqDec eqb_CCA_OracleResponse eqb_CCA_OracleResponse_leibniz).
  Qed.

  Section KeyExchange_IND_CCA_ROM.

  Variable A : PublicInit -> PublicResponse -> SharedSecret -> Aux -> OracleComp CCA_OracleQuery CCA_OracleResponse bool. 

  Variable rndRange : Comp RangeRO.

  Definition ccaOracle_ROM(k : PrivateKey)(r : PublicResponse)( _ : unit)(q : CCA_OracleQuery) :  OracleComp DomainRO RangeRO (CCA_OracleResponse  * unit) :=
    match q with
    | cca_oq_ro d => r <--$ OC_Query _ d; $ret (cca_or_ro r, tt)
    | cca_oq_dec resp => 
      if (resp ?= r) then ($ret (cca_or_dec None, tt)) else
      r <--$ decapsFunc_ROM k resp; $ret (cca_or_dec r, tt)
    end.

   Variable rndSharedSecret : Comp SharedSecret.

  Definition KeyExchangeCCA_ROM_G0 :=
    [sk, P] <--$2 keyGen_ROM;
    r_opt <--$ responseFunc_ROM P;
    match r_opt with
    | None => $ret false
    | Some (k, R, a) => 
      [z, _] <--$2 OC_Run _ _ _ (A P R k a) (ccaOracle_ROM sk R) tt;
      $ ret z
    end.

  Definition KeyExchangeCCA_ROM_G1 :=
    [sk, P] <--$2 keyGen_ROM;
    r_opt <--$ responseFunc_ROM P;
    match r_opt with
    | None => $ret false
    | Some (_, R, a) => 
       k <--$$ rndSharedSecret;
      [z, _] <--$2 OC_Run _ _ _ (A P R k a) (ccaOracle_ROM sk R) tt;
      $ ret z
    end.


  Definition KeyExchangeCCA_O_Advantage :=
    | Pr[ExpROM _ _ rndRange _ KeyExchangeCCA_ROM_G0] - Pr[ExpROM _ _ rndRange _ KeyExchangeCCA_ROM_G1] |.

  End KeyExchange_IND_CCA_ROM.
End KeyExchange_CCA_ROM.




