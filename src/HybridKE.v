(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: MIT-0 *)

Set Implicit Arguments.

Require Import FCF.
Require Import FCF.CompFold.
Require Import FCF.PRF.
Require Import Permutation.

Require Import KeyExchange.

Local Open Scope list_scope.

Theorem maybeBind_right_ident : forall (A : Type)(a : option A),
  (x <-? a; Some x) = a.

  intros.
  destruct a; reflexivity.

Qed.

Theorem maybeBind_assoc : forall (A B C: Type) (a : option A)(f : A -> option B)(g : B -> option C),
  Comp.maybeBind (Comp.maybeBind a f) g = Comp.maybeBind a (fun x => Comp.maybeBind (f x) g).

  intros.
  destruct a; reflexivity.

Qed.

Fixpoint stripOpt(A : Type)(ls : list (option A)) : option (list A) :=
  match ls with
  | nil => Some nil
  | a :: z =>
    a' <-? a;
    z' <-? stripOpt z;
    Some (a' :: z')
  end.

Theorem maybeBind_seq_eq : forall (A B : Type)(a : option A)(f1 f2 : A -> option B),
  (forall x, (f1 x) = (f2 x)) ->
  Comp.maybeBind a f1 = Comp.maybeBind a f2.

  intros. destruct a; simpl. eauto. 
  reflexivity.

Qed.

Theorem stripOpt_app : forall (A : Type)(ls1 ls2 : list (option A)),
  stripOpt (ls1 ++ ls2) = (x <-? stripOpt ls1; y <-? stripOpt ls2; Some (x ++ y)).

  induction ls1; intuition; simpl in *.
  symmetry.
  eapply maybeBind_right_ident.
  rewrite maybeBind_assoc.
  eapply maybeBind_seq_eq; intros.
  rewrite IHls1.
  rewrite maybeBind_assoc.
  rewrite maybeBind_assoc.
  eapply maybeBind_seq_eq; intros.
  rewrite maybeBind_assoc.
  reflexivity.

Qed.

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

  Definition KDF := Secret -> Salt -> Context -> nat -> OKM.
  Variable kdf : KDF.

  Variable RndOKM : nat -> Comp OKM.
  Variable defOKM : OKM.

  Section KDF_WeakSecure.

    Variable A_State : Set.
    Variable A1 : SecretAux -> Salt -> Comp (Context * nat * A_State).
    Variable A2 : A_State -> OKM -> Comp bool.
    Variable SaltGen : Comp Salt.

    Section KDF_SecureExact.
      Variable KeyGen : Comp (option (Secret * SecretAux)).

      (* This definition is weaker than usual---adversary is not given a 
          KDF oracle. *)
      Definition KDF_WeakG0 :=
        sa_opt <-$ KeyGen;
        match sa_opt with
        | None => ret false
        | Some (s, a) =>
          r <-$ SaltGen;
          [c, l, s_A] <-$3 A1 a r;
          okm <- kdf s r c l;
          A2 s_A okm
        end.

      Definition KDF_WeakG1 :=
        sa_opt <-$ KeyGen;
        match sa_opt with
        | None => ret false
        | Some (s, a) =>
          r <-$ SaltGen;
          [c, l, s_A] <-$3 A1 a r;
          okm <-$ RndOKM l;
          A2 s_A okm
        end.
      
      Definition WeakKDF_Advantage :=
        | Pr[KDF_WeakG0] - Pr[KDF_WeakG1] |.

    End KDF_SecureExact.
    
  End KDF_WeakSecure.

  Section KDF_Secure.

    Definition KDF_Oracle s r (c : option Context) (_ : unit) cl : Comp (OKM * unit) :=
      res <- kdf s r (fst cl) (snd cl);
      match c with
      | None => ret (res, tt)
      | Some c' => ret (if (eqb c' (fst cl)) then (defOKM, tt) else (res, tt))
      end.

    Variable A_State : Set.
    Variable A1 : SecretAux -> Salt -> OracleComp (Context * nat) OKM (Context * nat * A_State).
    Variable A2 : A_State -> OKM -> OracleComp (Context * nat) OKM bool.

    Section KDF_SecureExact.
      Variable KeyGen : Comp (Secret * SecretAux).
      Variable SaltGen : Comp Salt.

      Definition KDF_G0 :=
        [s, a] <-$2 KeyGen;
        r <-$ SaltGen;
        [r_a, _] <-$2 A1 a r _ _ (KDF_Oracle s r None) tt;
        [c, l, s_A] <-3 r_a;
        okm <- kdf s r c l;
        [r_a, _] <-$2 A2 s_A okm _ _ (KDF_Oracle s r (Some c)) tt;
        ret r_a.

      Definition KDF_G1 :=
        [s, a] <-$2 KeyGen;
        r <-$ SaltGen;
        [r_a, _] <-$2 A1 a r _ _ (KDF_Oracle s r None) tt;
        [c, l, s_A] <-3 r_a;
        okm <-$ RndOKM l;
        [r_a, _] <-$2 A2 s_A okm _ _ (KDF_Oracle s r (Some c)) tt;
        ret r_a.


    End KDF_SecureExact.

    Definition EntropySecureKDF m eps :=
      forall KeyGen SaltGen, 
      EntropySource _ _ KeyGen m ->
      | Pr[KDF_G0 KeyGen SaltGen] - Pr[KDF_G1 KeyGen SaltGen]| <= eps.
  End KDF_Secure.

  Section KDF_CR.

    Definition kdfProd p :=
      kdf (fst p) (fst (fst (snd p))) (snd (fst (snd p))) (snd (snd p)).

    Variable A : Comp ((Secret * Secret) * (Salt * Context * nat)).
    
    Definition KDF_CR := 
      [s1, s2, x] <-$3 A;
      ret (if (s1 ?= s2) then false else
        ((kdfProd (s1, x)) ?= (kdfProd (s2, x)))).

    Definition KDF_CR_Advantage := 
      Pr[KDF_CR].

  End KDF_CR.

End KDF.

Definition Octet := Bvector 8.
Definition OctetString := list Octet.
Definition OctetStringKDF := KDF OctetString OctetString OctetString OctetString.

Ltac OctetString_EqDec := repeat 
  match goal with
  | [|- EqDec (prod _ _) ] => apply pair_EqDec
  | [|- EqDec (list _) ] => apply list_EqDec
  | [|- EqDec OctetString ] => apply list_EqDec
  | [|- EqDec Octet ] => apply Bvector_EqDec
  | [|- EqDec (Bvector _) ] => apply Bvector_EqDec
  end.

Definition rndOctet := {0,1}^8.

Definition rndOctetString strLength :=
  compMap _ (fun _ => rndOctet) (forNats strLength).

Section CtKDF.
  
  Variable kdf : OctetStringKDF.
  Variable format : OctetString -> list OctetString -> list OctetString -> OctetString.
  Variable keyLength : nat.
  Variable psk : OctetString.
  Variable context : OctetString.
  Variable label : OctetString.

  Definition ctKDF k MA MB length :=
    let secret := psk ++ flatten k in
    let kdf_context := format context MA MB in
    kdf secret label kdf_context length.
  
  Definition OctetStringKE := (@KeyExchange OctetString OctetString OctetString OctetString _ _ ).
  Variable KE : list OctetStringKE.
  Variable defKE : OctetStringKE.

  Definition ctKeyGen (KE : list OctetStringKE) :=
    ls <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE; 
      ret (fst (split ls), snd (split ls)).

  Definition ctResponseFunc (KE : list OctetStringKE)(Ps : list OctetString) :=
    ls_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE Ps);
    ret (
      ls <-? stripOpt ls_opt;
      Rs <- snd (split ls); 
      k <- ctKDF (fst (split ls)) Ps Rs keyLength;
      Some (k, Rs)
    ).

  Instance CtKE : (@KeyExchange (list OctetString) (list OctetString) (list OctetString) OctetString _ _ ) := {
    keyGen := ctKeyGen KE;
    responseFunc := ctResponseFunc KE
    (*;receiveFunc := ctReceiveFunc KE *)
  }.

  Hypothesis keyGen_wf : forall ke, 
    In ke KE ->
    well_formed_comp (@keyGen _ _ _ _ _ _ ke).
  Hypothesis responseFunc_wf : forall ke x, 
    In ke KE ->
    well_formed_comp (@responseFunc _ _ _ _ _ _ ke x).
    
  (* assume an arbitrary "strong" KE scheme *)
  Variable strongKE : nat.
  Hypothesis strongKE_small : strongKE < length KE.

  (* Prove that we can split the list of key exchange operations at an arbitrary
    position and reorder them so that some chosen key exchange happens first. *)
  Section CtKDF_SplitReorder.

    Variable A : (list (OctetString * OctetString)) -> (list (option (OctetString * OctetString))) -> Comp bool.

    Definition CtKDF_SplitReorder_G0 :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE (snd (split lsSK)));
      (A lsSK lsR).

    Definition CtKDF_SplitReorder_G1 :=
      SK_strong <-$ @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      R_strong <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) (snd SK_strong) );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1 <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2 <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      (A (lsSK1 ++ (SK_strong :: lsSK2)) (lsR1 ++ (R_strong :: lsR2))).

    (* first split map operations *)
    Definition CtKDF_SplitReorder_G0a :=
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);
      SK_strong <-$ @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1 <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      R_strong <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) (snd SK_strong) );
      lsR2 <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      (A (lsSK1 ++ (SK_strong :: lsSK2)) (lsR1 ++ (R_strong :: lsR2))).

    Theorem CtKDF_SplitReorder_G0_G0a_equiv :  
       Pr[CtKDF_SplitReorder_G0] == Pr[CtKDF_SplitReorder_G0a].

      unfold CtKDF_SplitReorder_G0, CtKDF_SplitReorder_G0a.
      rewrite (@lsAppCons _ KE strongKE defKE) at 1; trivial.
      eapply eqRat_trans.
      eapply evalDist_seq_eq_trans.
      intros.
      eapply compMap_app.
      fcf_inline_first.
      fcf_skip.
      reflexivity.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      reflexivity.

      rewrite (@lsAppCons _ (combine KE (snd (split (x ++ x0 :: x1)))) strongKE (defKE, nil)) at 1; trivial.
      eapply eqRat_trans.
      eapply evalDist_seq_eq_trans.
      intros.
      eapply compMap_app.
      fcf_inline_first.
      fcf_skip.
      rewrite firstn_combine.
      rewrite firstn_snd_split_app_gen.
      reflexivity.
      assert (length x = length (firstn strongKE KE)).
      eapply compMap_length; eauto.
      rewrite H3.
      symmetry.
      apply firstn_length_le.
      omega.

      fcf_inline_first.
      fcf_skip.
      rewrite nth_combine. simpl.
      rewrite nth_snd_split_app_gen.
      rewrite nth_0_snd_split_cons.
      reflexivity.
      assert (length x = length (firstn strongKE KE)).
      eapply compMap_length; eauto.
      rewrite H4.
      symmetry.
      apply firstn_length_le.
      omega.
    
      rewrite snd_split_length.
      apply compMap_length in H2.
      apply compMap_length in H0.
      rewrite app_length. simpl.
      rewrite H0.
      rewrite H2.
      rewrite firstn_length_le.
      rewrite skipn_length.
      omega.
      omega.
     
      fcf_inline_first.
      fcf_skip.
      rewrite skipn_combine.
      rewrite skipn_snd_split_app_cons_gen.
      reflexivity.
      f_equal.
      assert (length x = length (firstn strongKE KE)).
      eapply compMap_length; eauto.
      rewrite H5.
      symmetry.
      apply firstn_length_le.
      omega.

      rewrite combine_length.
      rewrite min_l.
      trivial.    
      apply compMap_length in H0.
      apply compMap_length in H2.

      rewrite snd_split_app.
      rewrite snd_split_cons.
      repeat rewrite app_length.
      simpl.
      repeat rewrite snd_split_length.
      rewrite H0.
      rewrite H2.
      rewrite firstn_length_le.
      rewrite skipn_length.
      omega.
      omega.
    Qed.

    (* reorder *) 
    Theorem CtKDF_SplitReorder_G0a_G1_equiv :  
     Pr[CtKDF_SplitReorder_G0a] == Pr[CtKDF_SplitReorder_G1].

      unfold CtKDF_SplitReorder_G0a, CtKDF_SplitReorder_G1.
      fcf_swap leftc.
      fcf_skip.
      fcf_swap rightc.
      fcf_skip.
      fcf_swap rightc.
      fcf_skip.
      fcf_swap rightc.
      reflexivity.
    Qed.

    Theorem CtKDF_SplitReorder_equiv : 
      Pr[CtKDF_SplitReorder_G0] == Pr[CtKDF_SplitReorder_G1].

      rewrite CtKDF_SplitReorder_G0_G0a_equiv.
      apply CtKDF_SplitReorder_G0a_G1_equiv.

    Qed.

  End CtKDF_SplitReorder.


  (* Assume a distribution on octet strings that has a certain amount of entropy *)
  Variable rndSharedSecret : Comp OctetString. 
  Hypothesis rndSharedSecret_wf : well_formed_comp rndSharedSecret.
  Variable rndSecretEps : Rat.
  Hypothesis rndSharedSecret_prob_le : forall b, 
    evalDist rndSharedSecret b <= rndSecretEps.

  Section CtKDF_IND_CPA.

  Variable A : (list OctetString) -> (list OctetString) -> OctetString -> Comp bool.

  (* constructed adversary against the strong KE scheme*)
  Definition StrongKE_A (P_strong R_strong k_strong: OctetString) : Comp bool:=
    let KE1 := firstn strongKE KE in
    let KE2 := skipn (S strongKE) KE in
    lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE1;
    sk1 <- fst (split lsSK1);
    P1 <- snd (split lsSK1);
    lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE2;
    sk2 <- fst (split lsSK2);
    P2 <- snd (split lsSK2);

    lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE1 P1);
    lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE2 P2);
    match (
      lsR1 <-? stripOpt lsR1_opt;
      R1 <- snd (split lsR1); 
      lsK1 <- fst (split lsR1);  
      lsR2 <-? stripOpt lsR2_opt;
      R2 <- snd (split lsR2); 
      lsK2 <- fst (split lsR2);
      k <- ctKDF (lsK1 ++ (k_strong :: lsK2)) (P1 ++ P_strong :: P2) (R1 ++ R_strong :: R2) keyLength;
      (Some (k, (R1 ++ R_strong :: R2)))
    ) with
    | None => ret false
    | Some (k, R) => A (P1 ++ P_strong :: P2) R k
    end.
    

  (* constructed adversary against the KDF *)
  Definition KDF_A1 a (r : OctetString) :=
    ret ((format context (fst a) (snd a)), keyLength, a).

  Definition KDF_A2 s_A okm :=
    (A (fst s_A) (snd s_A) okm).

  (* We cannot assume that the KDF is a generic extractor, because there is no salt. *)
  (* Instead, we assume something weaker, that the KDF is an extractor for any string containing
    a random shared secret from a given distribution. *)
  (* In this assumption, an adversary determines the rest of the source distribution. *)
  Definition StrongKE_KeyGen (A : Comp (option (OctetString * OctetString * (list OctetString * list OctetString)))) := 
    k_strong <-$ rndSharedSecret; 
    xOpt <-$ A;
    ret (
      x <-? xOpt;
      [s1, s2, aux] <-3 x;
      Some (s1 ++ k_strong ++ s2, aux)
    ).
  
  (* The constructed adversary that determines the rest of the source distribution *)
  Definition KDF_KeyGen_A := 
    
    let KE_strong := nth strongKE KE defKE in

    [_, P_strong] <-$2 @keyGen _ _ _ _ _ _ KE_strong;
    krStrong_opt <-$ @responseFunc _ _ _ _ _ _ KE_strong P_strong;
    let KE1 := firstn strongKE KE in
    let KE2 := skipn (S strongKE) KE in

    lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE1;
    P1 <- snd (split lsSK1);

    lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE2;
    P2 <- snd (split lsSK2);

    lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE1 P1);
    lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE2 P2);
    ret (
      krStrong <-? krStrong_opt;
      R_strong <- snd krStrong;
      lsR1 <-? stripOpt lsR1_opt;
      R1 <- snd (split lsR1); 
      lsK1 <- fst (split lsR1);
      lsR2 <-? stripOpt lsR2_opt;
      R2 <- snd (split lsR2); 
      lsK2 <- fst (split lsR2);
      Some ((psk ++ (flatten lsK1), (flatten lsK2)), (P1 ++ P_strong :: P2, R1 ++R_strong :: R2))
    ).

  Definition kdfAdvantage :=
    @WeakKDF_Advantage _ _ _ _ _ kdf rndOctetString _ KDF_A1 KDF_A2 (ret label) (StrongKE_KeyGen KDF_KeyGen_A). 
  
  Definition strongKE_Advantage := (@KeyExchangeCPA_Advantage _ _ _ _ _ _ 
      (nth strongKE KE defKE) rndSharedSecret StrongKE_A).

  (* inline and simplify *)
  Definition CtKDF_G1 :=
    lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
    sk <- fst (split lsSK);
    P <- snd (split lsSK);
    lsR_opts <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE P);
    lsR_opt <- stripOpt lsR_opts;
    kr_opt <- (
      lsR <-? lsR_opt;
      R <- snd (split lsR); 
      lsK <- fst (split lsR);
      k <- ctKDF lsK P R keyLength;
      Some (k, R)
    );
    match kr_opt with
    | None => ret false
    | Some (k, R) => A P R k
    end.

  Theorem CtKDF_G1_equiv :  
    Pr[(@KeyExchangeCPA_G0 _ _ _ _ _ _ CtKE A)] == Pr[CtKDF_G1].

    unfold KeyExchangeCPA_G0, keyGen, responseFunc, CtKE, 
      ctKeyGen, ctResponseFunc, CtKDF_G1.
    repeat (fcf_inline_first; fcf_skip).
  Qed.

  (* Split list at strong ke, use constructed adversary *)
  Definition CtKDF_G2 := 
    
    let KE_strong := nth strongKE KE defKE in

    [_, P_strong] <-$2 @keyGen _ _ _ _ _ _ KE_strong;
    krStrong_opt <-$ @responseFunc _ _ _ _ _ _ KE_strong P_strong;
    match krStrong_opt with
    | None => ret false
    | Some (k, R) => StrongKE_A P_strong R k
    end.

  (* remove let bindings *)
  Definition CtKDF_G1a :=
    lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
    lsR_opts <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE (snd (split lsSK)));
    match (stripOpt lsR_opts) with
    | None => ret false
    | Some lsR =>
      (A (snd (split lsSK)) (snd (split lsR)) (ctKDF (fst (split lsR)) (snd (split lsSK)) (snd (split lsR)) keyLength))
    end.

  Theorem CtKDF_G1_G1a_equiv :  
    Pr[CtKDF_G1] == Pr[CtKDF_G1a].

    unfold CtKDF_G1, CtKDF_G1a.
    repeat (fcf_simp; fcf_skip).
    unfold Comp.maybeBind.
    symmetry.
    match goal with
    | [|- context[match ?a with |Some _ => _ | None => _ end] ] =>
      destruct a
    end;
    reflexivity.

  Qed.

  (* split and reorder *)
  Definition CtKDF_G1b :=
    SK_strong <-$ @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
    R_strong_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) (snd SK_strong) );
    lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
    lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
    lsR1_opts <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
    lsR2_opts <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
    match (stripOpt (lsR1_opts ++ R_strong_opt :: lsR2_opts)) with
    | None => ret false
    | Some R => 
    (A ((snd (split lsSK1))++(snd SK_strong)::(snd (split lsSK2))) (snd (split R))
      (ctKDF 
        (fst (split R))
        ((snd (split lsSK1))++(snd SK_strong)::(snd (split lsSK2))) 
        (snd (split R))
        keyLength))
    end.

  Definition CtKDF_G1a_A (lsSK : list (OctetString * OctetString)) (lsR : list (OctetString * OctetString)):=
    (A (snd (split lsSK)) (snd (split lsR)) 
      (ctKDF (fst (split lsR)) (snd (split lsSK)) (snd (split lsR)) keyLength)).


  Theorem CtKDF_G1a_G1b_equiv :  
     Pr[CtKDF_G1a] == Pr[CtKDF_G1b].

    unfold CtKDF_G1a, CtKDF_G1b.
    eapply eqRat_trans.
    apply (CtKDF_SplitReorder_equiv).    
    unfold CtKDF_SplitReorder_G1.
    repeat (fcf_skip).
    repeat rewrite snd_split_app. 
    repeat rewrite fst_split_app.
    repeat rewrite snd_split_cons.
    repeat rewrite fst_split_cons.
    reflexivity.
  Qed.

  (* put let bindings back in *)
  Theorem CtKDF_G1b_G2_equiv :  
     Pr[CtKDF_G1b] == Pr[CtKDF_G2].

    unfold CtKDF_G1b, CtKDF_G2, StrongKE_A.
    repeat (fcf_simp; fcf_skip).
    reflexivity.
    case_eq x; intros.
    destruct p.
    do 4 fcf_skip.
    rewrite stripOpt_app.
    destruct (stripOpt x1).
    + simpl.
    destruct (stripOpt x2).
    * simpl.
    repeat rewrite snd_split_app. 
    repeat rewrite fst_split_app.
    repeat rewrite snd_split_cons.
    repeat rewrite fst_split_cons.
    reflexivity.
    * simpl.
    reflexivity.
    + simpl.
    reflexivity.

    + subst.
    fcf_irr_l.
    eapply compMap_wf; intuition.
    eapply keyGen_wf.
    eapply firstn_In; eauto.
    fcf_irr_l.
    eapply compMap_wf; intuition.
    eapply keyGen_wf.
    destruct KE; trivial.
    simpl. right.
    eapply skipn_In; eauto.
    fcf_irr_l.
    eapply compMap_wf; intuition.
    eapply responseFunc_wf.
    destruct a; simpl in *.
    eapply firstn_In.
    eapply in_combine_l; eauto.
    fcf_irr_l.
    eapply compMap_wf; intuition.
    eapply responseFunc_wf.
    destruct KE; trivial.
    simpl. right.
    destruct a; simpl in *.
    eapply skipn_In.
    eapply in_combine_l; eauto.
    rewrite stripOpt_app.
    destruct (stripOpt x1); simpl;  reflexivity.
    
  Qed.

  Theorem CtKDF_G2_equiv :  
     Pr[CtKDF_G1] == Pr[CtKDF_G2].
  
    rewrite CtKDF_G1_G1a_equiv.
    rewrite CtKDF_G1a_G1b_equiv.
    apply CtKDF_G1b_G2_equiv.
  Qed.

  (* apply security assumption for strong KE *)
  Definition CtKDF_G3 := 
    
    let KE_strong := nth strongKE KE defKE in

    [sk_strong, P_strong] <-$2 @keyGen _ _ _ _ _ _ KE_strong;
    R_opt <-$ @responseFunc _ _ _ _ _ _ KE_strong P_strong;
    match R_opt with
    | None => ret false
    | Some (_, R_strong) => 
        k_strong <-$ rndSharedSecret;
        StrongKE_A P_strong R_strong k_strong
    end.

  Theorem CtKDF_G3_close :  
     | Pr[CtKDF_G2] - Pr[CtKDF_G3] | == strongKE_Advantage.

    reflexivity.

  Qed.

  (* inline KE constructed adversary and put game in correct form to use KDF assumption*)
  Definition KDF_KeyGen := 
    
    let KE_strong := nth strongKE KE defKE in

    [_, P_strong] <-$2 @keyGen _ _ _ _ _ _ KE_strong;
    R_opt <-$ @responseFunc _ _ _ _ _ _ KE_strong P_strong;   
    k_strong <-$ rndSharedSecret;

    let KE1 := firstn strongKE KE in
    let KE2 := skipn (S strongKE) KE in

    lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE1;
    P1 <- snd (split lsSK1);

    lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE2;
    P2 <- snd (split lsSK2);

    lsR1_opts <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE1 P1);
    lsR2_opts <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE2 P2);
    ret (
      lsR1 <-? stripOpt lsR1_opts;
      lsR2 <-? stripOpt lsR2_opts;
      R <-? R_opt;
      
      Some (psk ++ flatten ((fst (split lsR1)) ++ k_strong :: (fst (split lsR2))), (P1 ++ P_strong :: P2, (snd (split lsR1))++(snd R) :: (snd (split lsR2))))
    ).

  Definition CtKDF_G4 := 
    r <-$ ret label;
    x_opt <-$ KDF_KeyGen;
    match x_opt with
    | None => ret false
    | Some (s, a) => 
      [c, l, s_A] <-$3 KDF_A1 a r;
      okm <- kdf s r c l;
      KDF_A2 s_A okm
    end.

  Theorem CtKDF_G4_equiv : 
    Pr[CtKDF_G3] == Pr[CtKDF_G4].

    Local Opaque evalDist.

    unfold CtKDF_G3, CtKDF_G4.
    unfold StrongKE_A, KDF_KeyGen, KDF_A1, KDF_A2, ctKDF.
    fcf_simp.
    fcf_inline_first; fcf_skip; fcf_simp.
    fcf_inline_first; fcf_skip; fcf_simp.
    destruct x.
    destruct p.
    fcf_inline_first; fcf_skip; fcf_simp.
    fcf_inline_first; fcf_skip; fcf_simp.
    fcf_inline_first; fcf_skip; fcf_simp.
    fcf_inline_first; fcf_skip; fcf_simp.
    fcf_inline_first; fcf_skip; fcf_simp.
    case_eq (stripOpt x2); intros.
    simpl.
    case_eq (stripOpt x3); intros.
    simpl.
    fcf_simp.
    simpl.
    reflexivity.
    reflexivity.
    reflexivity.
    
    fcf_inline_first.
    fcf_irr_r.
    fcf_inline_first.
    fcf_irr_r.
    eapply compMap_wf; intros.
    eapply keyGen_wf.
    eapply firstn_In; eauto.
    fcf_inline_first.
    fcf_irr_r.
    eapply compMap_wf; intros.
    destruct KE; simpl in *; intuition idtac.
    eapply keyGen_wf.
    right.
    eapply skipn_In; eauto.
    fcf_inline_first.
    fcf_irr_r.
    eapply compMap_wf.
    intros.
    eapply responseFunc_wf.  
    destruct a. simpl in *.
    eapply firstn_In.
    eapply in_combine_l; eauto.
    fcf_inline_first.
    fcf_irr_r.
    eapply compMap_wf.
    intros.
    eapply responseFunc_wf.  
    destruct a. simpl in *.
    destruct KE; simpl in *; intuition idtac.
    right.
    eapply skipn_In.
    eapply in_combine_l; eauto.
 
    fcf_simp.
    destruct (stripOpt x2).
    simpl.
    destruct (stripOpt x3).
    simpl.
    reflexivity.
    reflexivity.
    reflexivity.

    Local Transparent evalDist.
    
  Qed.

  (* apply KDF definition to replace okm with random *)
  Definition CtKDF_G5 := 
    r <-$ ret label;
    x_opt <-$ KDF_KeyGen;
    match x_opt with
    | None => ret false
    | Some (s, a) => 
      [c, l, s_A] <-$3 KDF_A1 a r;
      okm <-$ rndOctetString l;
      KDF_A2 s_A okm
    end.

  (* Need to prove that KDF source distribution is of the correct form.
    Transform KDF_KeyGen to make this easier. *)
  (* move secret generation to the end so we can factor it out of the repeat *)
  Theorem KDF_KeyGen_A_wf : 
    well_formed_comp KDF_KeyGen_A.

    unfold KDF_KeyGen_A.
    wftac.
    eapply keyGen_wf.
    apply nth_In.
    trivial.
    apply responseFunc_wf.
    apply nth_In.
    trivial.
    apply compMap_wf.
    intros.
    apply keyGen_wf.
    eapply firstn_In; eauto.
    apply compMap_wf.
    intros.
    apply keyGen_wf.
    eapply skipn_In.
    eauto.
    apply compMap_wf.
    intros.
    apply responseFunc_wf.
    destruct a. simpl in *.
    eapply in_combine_l in H4.
    eapply firstn_In.
    eauto.
    apply compMap_wf.
    intros. 
    apply responseFunc_wf.
    destruct a. simpl.
    apply in_combine_l in H5.
    eapply skipn_In.
    eauto.

  Qed.

  Theorem KDF_KeyGen_strong_equiv : 
    forall x,
    evalDist KDF_KeyGen x == evalDist (StrongKE_KeyGen KDF_KeyGen_A) x.

    intuition.
    unfold StrongKE_KeyGen, KDF_KeyGen, KDF_KeyGen_A.
    fcf_at fcf_inline rightc 1%nat.
    fcf_swap rightc.
    fcf_skip.
    fcf_simp.
    fcf_inline_first; fcf_swap leftc; fcf_skip; fcf_simp.
    fcf_inline_first; fcf_skip.
    fcf_inline_first; fcf_skip.
    fcf_inline_first; fcf_skip.
    fcf_inline_first; fcf_skip.
    fcf_inline_first; fcf_skip.
    fcf_simp.
    eapply evalDist_ret_eq.
    destruct x1; simpl.
    destruct (stripOpt x4); simpl.
    destruct (stripOpt x5); simpl.
    repeat rewrite flatten_app.
    rewrite app_assoc.
    reflexivity.
    trivial.
    trivial.
    destruct (stripOpt x4); simpl.
    destruct (stripOpt x5); simpl.
    trivial.
    trivial.
    trivial.
  Qed.

  Definition CtKDF_G4a := 
    r <-$ ret label;
    x_opt <-$ (StrongKE_KeyGen KDF_KeyGen_A);
    match x_opt with
    | None => ret false
    | Some (s, a) => 
      [c, l, s_A] <-$3 KDF_A1 a r;
      okm <- kdf s r c l;
      KDF_A2 s_A okm
    end.

  Theorem CtKDF_G4a_equiv :
    Pr[CtKDF_G4] == Pr[CtKDF_G4a].

    unfold CtKDF_G4, CtKDF_G4a.
    fcf_simp.
    eapply evalDist_seq_eq.
    intros.
    eapply KDF_KeyGen_strong_equiv.
    reflexivity.

  Qed.

  Definition CtKDF_G4b := 
    r <-$ ret label;
    x_opt <-$ (StrongKE_KeyGen KDF_KeyGen_A);
    match x_opt with
    | None => ret false
    | Some (s, a) => 
      [c, l, s_A] <-$3 KDF_A1 a r;
      okm <-$ rndOctetString l;
      KDF_A2 s_A okm
    end.

  Theorem CtKDF_G4b_G5_equiv :
    Pr[CtKDF_G4b] == Pr[CtKDF_G5].

    unfold CtKDF_G4b, CtKDF_G5.
    fcf_simp.
    eapply evalDist_seq_eq.
    intros.
    symmetry.
    eapply KDF_KeyGen_strong_equiv.
    intuition.

  Qed.

  Theorem CtKDF_G5_close: 
    | Pr[CtKDF_G4] - Pr[CtKDF_G5] | <= kdfAdvantage.

    rewrite <- CtKDF_G4b_G5_equiv.
    rewrite CtKDF_G4a_equiv.

    unfold kdfAdvantage, CtKDF_G4a, CtKDF_G4b, WeakKDF_Advantage, KDF_WeakG0, KDF_WeakG1.
    eapply eqRat_impl_leRat.
    eapply ratDistance_eqRat_compat.
    +fcf_simp.
    fcf_skip.
    destruct x. destruct p.
    fcf_simp.
    reflexivity.
    reflexivity.
    
    +fcf_simp.
    fcf_skip.
    destruct x. destruct p.
    fcf_simp.
    reflexivity.
    reflexivity.
  
  Qed.

  (* put everything back in the correct order*)
  Definition CtKDF_G6 :=
    lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
    sk <- fst (split lsSK);
    P <- snd (split lsSK);
    lsR_opts <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE P);
    lsR_opt <- stripOpt lsR_opts;
    match lsR_opt with
    | None => ret false
    | Some lsR => 
      R <- snd (split lsR); 
      lsK <- fst (split lsR);
      k <-$ rndOctetString keyLength;
      A P R k
    end.


  (* remove let bindings and remove unnecessary shared secret *)
  Definition CtKDF_G5a :=
  SK_strong <-$ @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
  R_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) (snd SK_strong) );
  lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
  lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
  lsR1_opts <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
  lsR2_opts <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
  okm <-$ rndOctetString keyLength;
  match (stripOpt (lsR1_opts ++ R_opt :: lsR2_opts)) with
  | None => ret false
  | Some lsR =>
    (A ((snd (split lsSK1))++(snd SK_strong)::(snd (split lsSK2))) (snd (split lsR))
      okm)
  end.

  Theorem CtKDF_G5_G5a_equiv :  
    Pr[CtKDF_G5] == Pr[CtKDF_G5a].

    Local Opaque evalDist.

    unfold CtKDF_G5, CtKDF_G5a, KDF_KeyGen, KDF_A1, KDF_A2.
    fcf_simp.
    fcf_inline_first; fcf_skip; fcf_simp.
    fcf_inline_first; fcf_skip; fcf_simp.
    reflexivity.  
    fcf_inline_first.
    fcf_irr_l.
    fcf_inline_first; fcf_skip; fcf_simp.
    fcf_inline_first; fcf_skip; fcf_simp.
    fcf_inline_first; fcf_skip; fcf_simp.
    fcf_inline_first; fcf_skip; fcf_simp.
    rewrite stripOpt_app.
    destruct (stripOpt x3).
    simpl.
    destruct (stripOpt x4).
    simpl.
    destruct x.
    simpl.
    fcf_simp.
    fcf_skip.
    simpl.
    rewrite snd_split_app.
    rewrite snd_split_cons.
    reflexivity.
    simpl.
    fcf_irr_r.
    eapply compMap_wf.
    intros.
    unfold rndOctet. wftac.
    simpl.
    fcf_irr_r.
    eapply compMap_wf.
    intros.
    unfold rndOctet. wftac.
    destruct x.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    simpl.
    fcf_irr_r.
    eapply compMap_wf.
    intros.
    unfold rndOctet. wftac.

    Local Transparent evalDist.
  Qed.

  (* reorder *)
  Definition CtKDF_G5b :=
    lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE); 
    SK_strong <-$ @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);   
    lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);

    lsR1_opts <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
    R_strong_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) (snd SK_strong) );    
    lsR2_opts <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
   
    okm <-$ rndOctetString keyLength;
    match (stripOpt (lsR1_opts ++ R_strong_opt :: lsR2_opts)) with
    | None => ret false
    | Some lsR => 
      (A ((snd (split lsSK1))++(snd SK_strong)::(snd (split lsSK2))) (snd (split lsR))
        okm)
    end.

  Theorem CtKDF_G5a_G5b_equiv :  
    Pr[CtKDF_G5a] == Pr[CtKDF_G5b].

    unfold CtKDF_G5a, CtKDF_G5b.
    fcf_swap rightc.
    fcf_skip.
    fcf_swap leftc.
    fcf_skip.
    fcf_swap leftc.
    fcf_skip.
    fcf_swap leftc.
    reflexivity.

  Qed.

  (* combine map operations *)
  Theorem CtKDF_G5b_G6_equiv :  
     Pr[CtKDF_G5b] == Pr[CtKDF_G6].

    unfold CtKDF_G5b, CtKDF_G6.
    symmetry.
    rewrite (@lsAppCons _ KE strongKE defKE) at 1; trivial.
    eapply eqRat_trans.
    eapply evalDist_seq_eq_trans.
    intros.
    eapply compMap_app.
    fcf_inline_first.
    fcf_skip.
    reflexivity.
    fcf_inline_first.
    fcf_skip.
    fcf_inline_first.
    fcf_skip.
    reflexivity.

    rewrite (@lsAppCons _ (combine KE (snd (split (x ++ x0 :: x1)))) strongKE (defKE, nil)) at 1; trivial.
    eapply eqRat_trans.
    eapply evalDist_seq_eq_trans.
    intros.
    eapply compMap_app.
    fcf_inline_first.
    fcf_skip.
    rewrite firstn_combine.
    rewrite firstn_snd_split_app_gen.
    reflexivity.
    assert (length x = length (firstn strongKE KE)).
    eapply compMap_length; eauto.
    rewrite H3.
    symmetry.
    apply firstn_length_le.
    omega.

    fcf_inline_first.
    fcf_skip.
    rewrite nth_combine. simpl.
    rewrite nth_snd_split_app_gen.
    rewrite nth_0_snd_split_cons.
    reflexivity.
    assert (length x = length (firstn strongKE KE)).
    eapply compMap_length; eauto.
    rewrite H4.
    symmetry.
    apply firstn_length_le.
    omega.
  
    rewrite snd_split_length.
    apply compMap_length in H2.
    apply compMap_length in H0.
    rewrite app_length. simpl.
    rewrite H0.
    rewrite H2.
    rewrite firstn_length_le.
    rewrite skipn_length.
    omega.
    omega.
   
    fcf_inline_first.
    fcf_skip.
    rewrite skipn_combine.
    rewrite skipn_snd_split_app_cons_gen.
    reflexivity.
    f_equal.
    assert (length x = length (firstn strongKE KE)).
    eapply compMap_length; eauto.
    rewrite H5.
    symmetry.
    apply firstn_length_le.
    omega.

    repeat rewrite snd_split_app.
    repeat rewrite fst_split_app.
    repeat rewrite snd_split_cons.
    repeat rewrite fst_split_cons.
    destruct (stripOpt (x2 ++ x3 :: x4)).
    reflexivity.
    fcf_irr_r.
    eapply compMap_wf.
    intros.
    unfold rndOctet. wftac.

    rewrite combine_length.
    rewrite min_l.
    trivial.    
    apply compMap_length in H0.
    apply compMap_length in H2.

    rewrite snd_split_app.
    rewrite snd_split_cons.
    repeat rewrite app_length.
    simpl.
    repeat rewrite snd_split_length.
    rewrite H0.
    rewrite H2.
    rewrite firstn_length_le.
    rewrite skipn_length.
    omega.
    omega.
  Qed.

  Theorem CtKDF_G6_equiv :  
     Pr[CtKDF_G5] == Pr[CtKDF_G6].
  
    rewrite CtKDF_G5_G5a_equiv.
    rewrite CtKDF_G5a_G5b_equiv.
    apply CtKDF_G5b_G6_equiv.
  Qed.

  (* the last game is a simplified form of the second game in the security definition *)
  Theorem CtKDF_G6_CPA_equiv :  
     Pr[CtKDF_G6] == Pr[(@KeyExchangeCPA_G1 _ _ _ _ _ _ CtKE (rndOctetString keyLength) A)].

    unfold CtKDF_G6, KeyExchangeCPA_G1.
    unfold CtKE, keyGen, ctKeyGen.
    fcf_inline_first; fcf_skip; fcf_simp.
    reflexivity.
    fcf_inline_first; fcf_skip; fcf_simp. 
    destruct (stripOpt x0);
    reflexivity.
  Qed.

  Theorem CtKE_secure : 
    @KeyExchangeCPA_Advantage _ _ _ _ _ _ CtKE (rndOctetString keyLength) A <= 
    strongKE_Advantage + kdfAdvantage.

    unfold KeyExchangeCPA_Advantage.
    rewrite CtKDF_G1_equiv.
    rewrite CtKDF_G2_equiv.
    eapply ratDistance_le_trans.
    apply eqRat_impl_leRat.
    apply CtKDF_G3_close.
    rewrite CtKDF_G4_equiv.
    rewrite <- CtKDF_G6_CPA_equiv.
    rewrite <- CtKDF_G6_equiv.
    apply CtKDF_G5_close.
  Qed.

End CtKDF_IND_CPA.

End CtKDF.
