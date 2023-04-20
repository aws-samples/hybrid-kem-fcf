(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: MIT-0 *)

Set Implicit Arguments.

Require Import FCF.
Require Import FCF.CompFold.
Require Import FCF.PRF.
Require Import Permutation.

Require Import KeyExchange.
Require Import HybridKE_Concatenate.

Local Open Scope list_scope.


Section EntropySource.

  Variable Secret SecretAux : Set.
  Hypothesis Secret_EqDec : EqDec Secret.
  Hypothesis SecretAux_EqDec : EqDec SecretAux.

  Variable KeyGen : Comp (Secret * SecretAux).

  Definition EntropySource_G s a :=
     [s', _] <-$2 Repeat KeyGen (fun p => eqb (snd p) a); 
     ret (eqb s s').

  Definition EntropySource m :=
    forall s a,
    In (s, a) (getSupport KeyGen) ->
    Pr[EntropySource_G s a] <= m.

End EntropySource.

Section KDF.

  Variable Secret Salt Context SecretAux OKM : Set.

  Hypothesis Secret_EqDec : EqDec Secret.
  Hypothesis SecretAux_EqDec : EqDec SecretAux.
  Hypothesis OKM_EqDec : EqDec OKM.
  Hypothesis Context_EqDec : EqDec Context.

  Definition KDF := Secret -> Salt -> Context  -> OKM.
  Variable kdf : KDF.

  Variable RndOKM : Comp OKM.
  Variable defOKM : OKM.

  Section KDF_WeakSecure.

    Variable A_State : Set.
    Variable A1 : SecretAux -> Salt -> Comp (Context * A_State).
    Variable A2 : A_State -> OKM -> Comp bool.
    Variable SaltGen : Comp Salt.

    Section KDF_SecureExact.
      Variable KeyGen : Comp (option (Secret * SecretAux)).

      (* This definition is weaker than usual---adversary is not given a 
          KDF oracle. *)
      Definition KDF_WeakG0 :=
        r <-$ SaltGen;
        s_opt <-$ KeyGen;
        match s_opt with
        | None => ret false
        | Some (s, a) => 
          [c, s_A] <-$2 A1 a r;
          okm <- kdf s r c;
          A2 s_A okm
        end.

    Definition KDF_WeakG1 :=
        r <-$ SaltGen;
        s_opt <-$ KeyGen;
        match s_opt with
        | None => ret false
        | Some (s, a) => 
          [c, s_A] <-$2 A1 a r;
          okm <-$ RndOKM;
          A2 s_A okm
        end.
      
      Definition WeakKDF_Advantage :=
        | Pr[KDF_WeakG0] - Pr[KDF_WeakG1] |.

    End KDF_SecureExact.

  End KDF_WeakSecure.

End KDF.



Section CtKDF.

  
  Variable Salt OKM Info : Set.
  Hypothesis OKM_EqDec : EqDec OKM.
  Hypothesis Info_EqDec : EqDec Info.
  Hypothesis Salt_EqDec : EqDec Salt.
  Variable rndOKM : Comp OKM.
  Variable kdf : KDF BitString Salt Info OKM.

  Variable PrivateKey : Set.
  Variable PublicInit : Set.
  Variable PublicResponse : Set.
  Variable Aux AuxInfo : Set.

  Hypothesis PrivateKey_EqDec : EqDec PrivateKey.
  Hypothesis PublicInit_EqDec : EqDec PublicInit.
  Hypothesis PublicResponse_EqDec : EqDec PublicResponse.
  Hypothesis Aux_EqDec : EqDec Aux.
  Hypothesis AuxInfo_EqDec : EqDec AuxInfo.

  Variable defAuxInfo : AuxInfo.

  Variable projectInfo : (list PublicInit * list PublicResponse * AuxInfo) -> Info.
  Variable label : Salt.

  Definition BitStringKE := (@BitStringKE PrivateKey PublicInit PublicResponse Aux _ ).

  (* Assume we have a strong KE *)
  Variable strongKE : BitStringKE.

  Variable strongKE_Pos : nat.
  Variable additionalSecretLengths : list nat.

  Definition KDF_OracleInput := (@KDF_OracleInput Salt Info).

  (* For all security definitions, there is an adversary procedure that sees the public outpus of the strong KE and produces the other KE outputs. 
  This adversary procedure models a number of KEs that are under the control of the adversary. *)
  Variable A_State : Set.
  Hypothesis A_State_EqDec : EqDec A_State.
  Variable A_KE : PublicInit -> PublicResponse -> OracleComp KDF_OracleInput OKM ((list (PublicInit * PublicResponse * BitString) * AuxInfo) * A_State).

  Definition KDF_Oracle(_ : unit) x :=
    let '(secret, salt, info) := x in
    ret (kdf secret salt info, tt).

  Definition ctKeyGen := (@ctKeyGen _ _ _ _ _ strongKE).

  Definition CtPublicResponse := (@CtPublicResponse PublicInit PublicResponse AuxInfo).

  Definition ctResponseFunc p := 
    x <-$ (((@ctResponseFunc Salt OKM Info _ PrivateKey PublicInit PublicResponse _ _ _ _ _ _ projectInfo label strongKE strongKE_Pos additionalSecretLengths A_State _ A_KE) p) _ _ KDF_Oracle tt);
    ret (fst x).

   Definition ctDecapsFunc  k r:= 
    x <-$ (((@ctDecapsFunc Salt OKM Info _ PrivateKey PublicInit PublicResponse _ _ _ projectInfo label strongKE strongKE_Pos additionalSecretLengths) k r) _ _ KDF_Oracle tt);
    ret (fst x).

  Instance CtKE : (@KeyExchange PrivateKey PublicInit CtPublicResponse (Aux * A_State) OKM  _ _ ) := {
    keyGen := ctKeyGen;
    responseFunc := ctResponseFunc;
    decapsFunc := ctDecapsFunc
  }.

  (* Assume a secure distribution on shared secrets. *)
  Variable rndSharedSecret : Comp BitString. 
  Hypothesis rndSharedSecret_wf : well_formed_comp rndSharedSecret.

  Section CtKDF_IND_CPA.

  Variable A : PublicInit -> CtPublicResponse -> OKM -> (Aux * A_State) -> Comp bool.

   Definition ctKDF_f k MA MB auxInfo : OKM :=
    let secret := flatten k in
    let kdf_context := projectInfo (MA, MB, auxInfo) in
    kdf secret label kdf_context.

  (* inline and simplify *)
  Definition CtKDF_G1 :=
    [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
    r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
    match r_opt with
    | None => ret false
    | Some (s, R, a) =>  
      [z, _] <-$2 (A_KE P R) _ _ KDF_Oracle tt;
      [ls, auxInfo, s_A] <-3 z;
      match (splitKdfInputs additionalSecretLengths ls strongKE_Pos) with
      | None => ret false
      | Some (Ps1, Rs1, s1, Ps2, Rs2, s2) =>
        k <- ctKDF_f (s1 ++ s :: s2) (Ps1 ++ P :: Ps2) (Rs1 ++ R :: Rs2) auxInfo;
        A P ((P, R), (ls, auxInfo)) k (a, s_A)
      end
    end.

  Theorem CtKDF_G1_equiv : 
    Pr[(@KeyExchangeCPA_G0 _ _ _ _ _ _ _ CtKE) A] == Pr[CtKDF_G1].

    unfold KeyExchangeCPA_G0, CtKDF_G1.
    fcf_sp.
    unfold ctKeyGen, HybridKE_Concatenate.ctKeyGen.
    fcf_sp.
    unfold ctResponseFunc, HybridKE_Concatenate.ctResponseFunc.
    fcf_sp.
    splitOpt; simpl; fcf_sp.
    fcf_skip.
    splitOpt; simpl; fcf_sp.
    eapply comp_spec_consequence.
    reflexivity.
    intuition idtac; subst; trivial.
  Qed.


  (* Apply IND-CPA assumption of strong KE to replace secret with random value *)
  Definition CtKDF_G2 :=
    [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
    r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
    match r_opt with
    | None => ret false
    | Some (_, R, a) =>  
      s <-$ rndSharedSecret;
      [z, _] <-$2 (A_KE P R) _ _ KDF_Oracle tt;
      [ls, auxInfo, s_A] <-3 z;
      match (splitKdfInputs additionalSecretLengths ls strongKE_Pos) with
      | None => ret false
      | Some (Ps1, Rs1, s1, Ps2, Rs2, s2) =>
        k <- ctKDF_f (s1 ++ s :: s2) (Ps1 ++ P :: Ps2) (Rs1 ++ R :: Rs2) auxInfo;
        A P ((P, R), (ls, auxInfo)) k (a, s_A)
      end
    end.

  Definition StrongKE_A P R s a :=
    [z, _] <-$2 (A_KE P R) _ _ KDF_Oracle tt;
    [ls, auxInfo, s_A] <-3 z;
    match (splitKdfInputs additionalSecretLengths ls strongKE_Pos) with
    | None => ret false
    | Some (Ps1, Rs1, s1, Ps2, Rs2, s2) =>
      k <- ctKDF_f (s1 ++ s :: s2) (Ps1 ++ P :: Ps2) (Rs1 ++ R :: Rs2) auxInfo;
      A P ((P, R), (ls, auxInfo)) k (a, s_A)
    end.

  Theorem CtKDF_G2_close : 
    | Pr[CtKDF_G1] - Pr[CtKDF_G2] | == (@KeyExchangeCPA_Advantage _ _ _ _ _ _ _ strongKE rndSharedSecret StrongKE_A).

    reflexivity.

  Qed.

  (* Prepare to apply the KDF security definition *)
  Definition KDF_KeyGen := 
    [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
    r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
    match r_opt with
    | None => ret None
    | Some (_, R, a) =>  
      s <-$ rndSharedSecret;
      [z, _] <-$2 (A_KE P R) _ _ KDF_Oracle tt;
      [ls, auxInfo, s_A] <-3 z;
      match (splitKdfInputs additionalSecretLengths ls strongKE_Pos) with
      | None => ret None
      | Some (Ps1, Rs1, s1, Ps2, Rs2, s2) =>
        ret (Some (flatten (s1 ++ s :: s2), (P, ((P, R), (ls, auxInfo)), (a, s_A))))
      end
    end.

  Definition KDF_A1 (a : (PublicInit * CtPublicResponse * (Aux * A_State))) (salt : Salt) :=
    let '(P, resp, s_A) := a in
    let '(R, x) := resp in
    let '(ls, auxInfo) := x in
    let '(P', R') := R in
    match (splitKdfInputs additionalSecretLengths  ls strongKE_Pos) with
    | None => ret (projectInfo (nil, nil, defAuxInfo), a)
    | Some (Ps1, Rs1, _, Ps2, Rs2, _) =>
      ret (projectInfo ((Ps1 ++ P :: Ps2), (Rs1 ++ R' :: Rs2), auxInfo) , a)
    end.

  Definition KDF_A2 (a : (PublicInit * CtPublicResponse * (Aux * A_State))) okm :=
    A (fst (fst a)) (snd (fst a)) okm (snd a).

  Definition CtKDF_G3 :=
    r <-$ (ret label);
    s_opt <-$ KDF_KeyGen;
    match s_opt with
    | None => ret false
    | Some (s, a) =>
      [c, s_A] <-$2 KDF_A1 a r;
      okm <- kdf s r c;
      KDF_A2 s_A okm
    end.

  Theorem CtKDF_G3_equiv : 
    Pr[CtKDF_G2] == Pr[CtKDF_G3].
  
    unfold CtKDF_G2, CtKDF_G3, KDF_KeyGen, KDF_A1, KDF_A2.
    fcf_sp.
    splitOpt; fcf_sp.
    splitOpt; fcf_sp.
    rewrite H7.
    fcf_sp.
    unfold ctKDF.
    eapply comp_spec_consequence.
    reflexivity.
    intuition idtac; subst; trivial.

  Qed.

  Definition CtKDF_G4 :=
    r <-$ (ret label);
    s_opt <-$ KDF_KeyGen;
    match s_opt with
    | None => ret false
    | Some (s, a) =>
      [c, s_A] <-$2 KDF_A1 a r;
      okm <-$ rndOKM;
      KDF_A2 s_A okm
    end.

  Theorem CtKDF_G4_close : 
    | Pr[CtKDF_G3] - Pr[CtKDF_G4] | == WeakKDF_Advantage kdf rndOKM KDF_A1 KDF_A2 (ret label) KDF_KeyGen.

    reflexivity.

  Qed.

  (* Inline and simplify. Remove the unnecessary shared secret *)
  Definition CtKDF_G5 :=
    [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
    r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
    match r_opt with
    | None => ret false
    | Some (_, R, a) =>  
      [z, _] <-$2 (A_KE P R) _ _ KDF_Oracle tt;
      [ls, auxInfo, s_A] <-3 z;
      match (splitKdfInputs additionalSecretLengths ls strongKE_Pos) with
      | None => ret false
      | Some (Ps1, Rs1, s1, Ps2, Rs2, s2) => 
        k <-$ rndOKM;
        A P ((P, R), (ls, auxInfo)) k (a, s_A)
      end
    end.

  Theorem CtKDF_G5_equiv : 
    Pr[CtKDF_G4] == Pr[CtKDF_G5].
  
    unfold CtKDF_G4, CtKDF_G5.
    fcf_sp.
    unfold KDF_KeyGen.
    fcf_sp.
    splitOpt; fcf_sp.
    fcf_irr_l.
    BitString_EqDec; eauto with typeclass_instances.
    fcf_sp.
    splitOpt; fcf_sp.
    rewrite H3.
    fcf_sp.
    unfold KDF_A2.
    simpl.
    eapply comp_spec_consequence.
    reflexivity.
    intuition idtac; subst; trivial.
  Qed.

  Theorem CtKDF_G5_CPA_equiv : 
    Pr[CtKDF_G5] == Pr[(@KeyExchangeCPA_G1 _ _ _ _ _ _ _ CtKE) (rndOKM) A].

    unfold CtKDF_G5, KeyExchangeCPA_G1.
    fcf_sp.
    unfold ctKeyGen, HybridKE_Concatenate.ctKeyGen.
    fcf_sp.
    unfold ctResponseFunc, HybridKE_Concatenate.ctResponseFunc.
    fcf_sp.
    splitOpt; fcf_sp.
    fcf_skip.
    splitOpt; fcf_sp.
    eapply comp_spec_consequence.
    reflexivity.
    intuition idtac; subst; trivial.

  Qed.

  Theorem CtKDF_CPA_Secure : 
    (@KeyExchangeCPA_Advantage _ _ _ _ _ _ _ CtKE (rndOKM) A) <= 
      (@KeyExchangeCPA_Advantage _ _ _ _ _ _ _ strongKE rndSharedSecret StrongKE_A) + 
      WeakKDF_Advantage kdf rndOKM KDF_A1 KDF_A2 (ret label) KDF_KeyGen.

    unfold KeyExchangeCPA_Advantage.
    rewrite CtKDF_G1_equiv.
    eapply ratDistance_le_trans.
    eapply eqRat_impl_leRat.
    apply CtKDF_G2_close.
    rewrite CtKDF_G3_equiv.
    eapply leRat_trans.
    eapply ratDistance_le_trans.
    eapply eqRat_impl_leRat.
    eapply CtKDF_G4_close.
    rewrite CtKDF_G5_equiv.
    rewrite CtKDF_G5_CPA_equiv.
    eapply eqRat_impl_leRat.
    apply (@ratIdentityIndiscernables (Pr [KeyExchangeCPA_G1 (rndOKM) A ] )).
    reflexivity.
    rewrite <- ratAdd_0_r.
    reflexivity.
  Qed.

End CtKDF_IND_CPA.

End CtKDF.
