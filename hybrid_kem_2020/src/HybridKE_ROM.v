(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: MIT-0 *)

Set Implicit Arguments.

Require Import FCF.
Require Import FCF.CompFold.
Require Import FCF.OracleCompFold.
Require Import FCF.PRF.
Require Import FCF.ROM.
Require Import Permutation.

Require Import KeyExchange_ROM.
Require Import KeyExchange.
Require Import HybridKE.

Local Open Scope list_scope.

Definition Octet := Bvector 8.
Definition OctetString := list Octet.

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

Definition beginsWith (A : Set)(eqd : EqDec A)(ls1 ls2 : list A) :=
  eqb (firstn (length ls2) ls1) ls2.

Fixpoint isSubListOf (A : Set)(eqd : EqDec A)(ls1 ls2 : list A) :=
  beginsWith _ ls2 ls1 ||
  match ls2 with
  | nil => false
  | a :: ls2' => isSubListOf _ ls1 ls2'
  end.

Theorem arrayLookup_any_dec_eq : 
  forall (A B : Set)(eqda : EqDec A) (ls : list (A * B)) q,
  (if
    arrayLookup _ ls q
   then true
   else false) =
  any_dec (fun x => eqb q (fst x)) ls.

  induction ls; unfold any_dec; intros; simpl in *.
  trivial.
  destruct a.
  case_eq (eqb q a); intros.
  rewrite eqb_leibniz in H.
  subst.
  simpl.
  rewrite eqb_refl.
  rewrite fold_left_orb_true.
  trivial.
  simpl.
  rewrite H.
  rewrite IHls.
  trivial.

Qed.

Ltac dest :=
  match goal with
  | [H : exists _, _ |- _] => destruct H
  end.

Theorem any_dec_true_ex : forall (A : Type)(f : A -> bool)(ls : list A),
  any_dec f ls = true <->
  exists a, In a ls /\ f a = true.

  unfold any_dec in *; induction ls; intuition; simpl in *.
  discriminate.
  dest.
  intuition.
  case_eq (f a); intros.
  econstructor; eauto.
  rewrite H2 in H1.
  intuition.
  dest; intuition.
  econstructor; eauto.
  dest.
  intuition.
  subst.
  rewrite H3.
  apply fold_left_orb_true.
  case_eq (f a); intros.
  apply fold_left_orb_true.
  eapply H0.
  econstructor; intuition; eauto.

Qed.

Theorem beginsWith_nil_nil : forall (A : Set)(eqda : EqDec A)(ls : list A),
  beginsWith _ nil ls = true ->
  ls = nil.

  unfold beginsWith in *; intuition.
  rewrite firstn_nil in *.
  rewrite eqb_leibniz in H.
  subst. trivial.

Qed.

Theorem beginsWith_nil_true : forall (A : Set)(eqda : EqDec A)(ls : list A),
  beginsWith _ ls nil = true.

  unfold beginsWith in *; intuition.
  simpl.
  apply eqb_leibniz.
  trivial.

Qed.

Theorem beginsWith_refl : forall (A : Set)(eqda : EqDec A)(ls : list A),
  beginsWith _ ls ls = true.

  unfold beginsWith in *; intuition.
  rewrite firstn_all.
  apply eqb_leibniz.
  trivial.

Qed.

Theorem beginsWith_app_true : forall (A : Set)(eqda : EqDec A)(ls1 ls2 ls3 : list A),
  beginsWith _ ls1 ls2 = true ->
  beginsWith _ (ls1 ++ ls3) ls2 = true.

  unfold beginsWith in *; intuition.
  rewrite eqb_leibniz in H. 
  destruct (le_dec (length ls1) (length ls2)).
  rewrite firstn_all2 in H; intuition.
  subst.
  rewrite firstn_app_eq.
  apply eqb_refl.
  rewrite firstn_app.
  cutrewrite ((length ls2 - length ls1) = O).
  simpl.
  rewrite app_nil_r.
  rewrite H.
  apply eqb_leibniz. trivial.
  lia.
Qed.

Theorem isSubListOf_nil_true : forall (A : Set)(eqda : EqDec A)(ls : list A),
  isSubListOf _ nil ls = true.

  induction ls; intuition; simpl in *.
  rewrite beginsWith_nil_true. trivial.

  rewrite IHls.
  apply orb_true_r.
  
Qed.

Theorem isSubListOf_app : forall (A : Set)(eqd : EqDec A)(ls2 ls3 ls1 : list A),
  (isSubListOf _ ls1 ls2 || isSubListOf _ ls1 ls3 = true) ->
  isSubListOf _ ls1 (ls2 ++ ls3) = true.

  induction ls2; intuition; simpl in *.
  case_eq (beginsWith eqd nil ls1); intros.
  apply beginsWith_nil_nil in H0.
  subst.
  eapply isSubListOf_nil_true.
  rewrite H0 in H.
  simpl in *.
  trivial.
  
  case_eq (beginsWith eqd (a :: ls2) ls1); intros;
  rewrite H0 in H.
  rewrite app_comm_cons.
  rewrite beginsWith_app_true.
  trivial.
  trivial.
  
  simpl in *.
  rewrite IHls2.
  apply orb_true_r.
  trivial.
  
Qed.

Theorem isSubListOf_refl : forall (A : Set)(eqda : EqDec A)(ls : list A),
  isSubListOf _ ls ls = true.

  induction ls; intuition; simpl in *.
  rewrite beginsWith_nil_true. trivial.
  rewrite beginsWith_refl. trivial.

Qed.


Section CtKDF_ROM.

  Variable format : OctetString -> list OctetString -> list OctetString -> OctetString.
  Variable keyLength : nat.
  Variable psk : OctetString.
  Variable context : OctetString.
  (* Model the KDF for each label and length as a RO with range of the correct length. 
  So the label doesn't actually appear in the model. *)
  (*Variable label : OctetString.*)

  (* The domain is context * secret *)
  Definition DomainRO := (OctetString * OctetString)%type.
  (* values in range have length keyLength *)
  Definition RangeRO := OctetString. 
  Definition rndRange := rndOctetString keyLength.

  Definition kdf := (@randomFunc DomainRO _ (rndOctetString keyLength) _).
  
  Definition ctKDF k MA MB : OracleComp DomainRO RangeRO RangeRO :=
    let secret := psk ++ flatten k in
    let kdf_context := format context MA MB in
    query (kdf_context, secret).
  
  Definition OctetStringKE := (@KeyExchange OctetString OctetString OctetString OctetString _ _).
  Variable KE : list OctetStringKE.
  Variable defKE : OctetStringKE.

  Hypothesis keyGen_wf : forall ke, 
    In ke KE ->
    well_formed_comp (@keyGen _ _ _ _ _ _ ke).
  Hypothesis responseFunc_wf : forall ke x, 
    In ke KE ->
    well_formed_comp (@responseFunc _ _ _ _ _ _ ke x).

  Definition ctKeyGen (KE : list OctetStringKE) : OracleComp DomainRO RangeRO (list OctetString * list OctetString) :=
    ls <--$$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE; 
    $ret (fst (split ls), snd (split ls)).

  Definition ctResponseFunc (KE : list OctetStringKE)(Ps : list OctetString) : OracleComp DomainRO RangeRO (option (OctetString * list OctetString)) :=
    ls_opt <--$$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE Ps);
    match (stripOpt ls_opt) with
    | None => $ret None
    | Some ls =>
      Rs <- snd (split ls); 
      k <--$ ctKDF (fst (split ls)) Ps Rs;
      $ret Some (k, Rs)
    end.

  Instance CtKE : (@KeyExchange_ROM (list OctetString) (list OctetString) (list OctetString) OctetString DomainRO RangeRO _ _ ) := {
    keyGen_ROM := ctKeyGen KE;
    responseFunc_ROM := ctResponseFunc KE
  }.
    
  (* assume an arbitrary "strong" KE scheme *)
  Variable strongKE : nat.
  Hypothesis strongKE_small : strongKE < length KE.
  
  Theorem rndRange_wf : 
    well_formed_comp rndRange.

    unfold rndRange, rndOctetString.
    eapply compMap_wf.
    intros.
    unfold rndOctet.
    wftac.

  Qed.

  Instance OctetString_EqDec : EqDec OctetString.

    unfold OctetString.
    eauto with typeclass_instances.

  Defined.

  Instance DomainRO_EqDec : EqDec DomainRO.

    unfold DomainRO.
    eauto with typeclass_instances.

  Defined.

  Hint Resolve rndRange_wf : wf.

  Ltac destOpt := 
    match goal with
    | [ |- context[match ?a with | Some _ => _ | None => _ end] ] =>
      case_eq a; intros
    end.

  Ltac someInv := 
    match goal with
    | [H: Some ?a = Some ?b |- _ ] =>
      inversion H; clear H; subst
    end.

  Ltac eqbPair_prop_inv :=
      match goal with
      | [H: eqbPair _ _ _ _ = true |- _ ] =>
        apply eqbPair_prop in H
      end.

  Section CtKDF_IND_CPA_ROM.

    Definition rndSharedSecret := rndOctetString keyLength.

    Variable A : (list OctetString) -> (list OctetString) -> OctetString -> OracleComp DomainRO RangeRO bool.
    Hypothesis A_wf : forall x y z, well_formed_oc (A x y z).

    (* unfold definitions and simplify *)
    Definition CtKDF_IND_CPA_G1 :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$
        compMap _
          (fun
             p => (@responseFunc _ _ _ _ _ _ (fst p) (snd p)))
          (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret false
      | Some lsR =>
        z1 <-$
        (
          Rs <- snd (split lsR);
          k <--$
          query (format context (snd (split lsSK)) Rs,
                psk ++ flatten (fst (split lsR))); 
          A (snd (split lsSK)) Rs k) _ _ 
        (randomFunc rndRange _) nil;
        ret (fst z1)
      end.

    Theorem CtKDF_IND_CPA_G1_equiv: 
      Pr [ExpROM _ _ rndRange _ (KeyExchangeCPA_ROM_G0 A) ] ==
      Pr [CtKDF_IND_CPA_G1].

      Local Opaque evalDist.
  
      unfold ExpROM, KeyExchangeCPA_ROM_G0, CtKDF_IND_CPA_G1.
      unfold keyGen, responseFunc, CtKE, ctResponseFunc.
      simpl.
      fcf_inline_first.
      simpl.
      fcf_skip.
      reflexivity.
      simpl.
      fcf_inline_first.
      fcf_skip.
      reflexivity.
      fcf_simp.
      destOpt.
      simpl.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_simp.
      simpl.
      fcf_skip.
      reflexivity.
      fcf_simp.
      reflexivity.

      fcf_inline_first.
      reflexivity.

      Local Transparent evalDist.

    Qed.

    (* run the query outside of the OracleComp *)
    Definition CtKDF_IND_CPA_G2 :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$
        compMap _
          (fun
             p => (@responseFunc _ _ _ _ _ _ (fst p) (snd p)))
          (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret false
      | Some lsR =>
        k <-$ rndRange; 
        z1 <-$
        (
          A (snd (split lsSK)) (snd (split lsR)) k) _ _ 
          (randomFunc rndRange _) (((format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR))),k)::nil);
          ret (fst z1)
      end.

    Theorem CtKDF_IND_CPA_G2_equiv: 
      Pr [CtKDF_IND_CPA_G1] == Pr [CtKDF_IND_CPA_G2].

      Local Opaque evalDist.

      unfold CtKDF_IND_CPA_G1, CtKDF_IND_CPA_G2.
      simpl.
      fcf_skip.
      fcf_skip.
      destOpt.
      fcf_inline_first.
      fcf_skip.
      reflexivity.
      reflexivity.     

      Local Transparent evalDist.
      
    Qed.

    (* Use a special form of a random oracle that keeps track of the new value *)
    Definition CtKDF_IND_CPA_G3 :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$
        compMap _
          (fun
             p => (@responseFunc _ _ _ _ _ _ (fst p) (snd p)))
          (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret false
      | Some lsR =>
        k <-$ rndRange; 
        z1 <-$
        (
          A (snd (split lsSK)) (snd (split lsR)) k) _ _ 
          (fun s q => if (q ?= (format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR)))) then ret (k, (((format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR))), k)::s)) else randomFunc rndRange _ s q) nil;
          ret (fst z1)
      end.

    Theorem CtKDF_IND_CPA_G3_equiv: 
      Pr [CtKDF_IND_CPA_G2] == Pr [CtKDF_IND_CPA_G3].

      eapply comp_spec_eq_impl_eq.

      unfold CtKDF_IND_CPA_G2, CtKDF_IND_CPA_G3.
      simpl.
      fcf_skip.
      fcf_skip.
      destOpt.
      fcf_skip.
      fcf_skip.
      eapply (@fcf_oracle_eq _ _
      (fun s1 s2 => 
      (arrayLookup _ s1 (format context (snd (split b)) (snd (split l)),
      psk ++ flatten (fst (split l))) = Some b1) /\
      forall x, (x <> (format context (snd (split b)) (snd (split l)),
      psk ++ flatten (fst (split l)))) -> arrayLookup _ s1 x = arrayLookup _ s2 x)
      ).
      intuition.
      simpl.
      rewrite eqbPair_refl.
      trivial.
      simpl.
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        case_eq a; intros
      end.
      apply eqbPair_prop in H7.
      subst.
      intuition.
      trivial.

      intuition.
      unfold randomFunc.  
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        case_eq a; intros
      end.
      apply eqbPair_prop in H6.
      subst.
      match goal with
      | [|- context[match ?a with | Some _ => _ | None => _ end] ] =>
        case_eq a; intros
      end.
      assert (Some l0 = Some b1).
      rewrite <- H6.
      rewrite <- H7.
      reflexivity.
      someInv.
      eapply comp_spec_ret; intuition.
      simpl.
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        case_eq a; intros
      end.
      
      eqbPair_prop_inv.
      intuition.
      eauto.
      assert (Some b1 = None).
      rewrite <- H6.
      rewrite <- H7.
      reflexivity.
      discriminate.

      rewrite H8.
      match goal with
      | [|- context[match ?a with | Some _ => _ | None => _ end] ] =>
        case_eq a; intros
      end.
      eapply comp_spec_ret; intuition.

      fcf_skip.
      eapply comp_spec_ret; intuition.
      simpl.
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        case_eq a; intros
      end.
      apply eqbPair_prop in H12.
      subst.
      rewrite eqbPair_refl in H6.
      discriminate.
      eauto.
      simpl.
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        case_eq a; intros
      end.
      trivial.
      eauto.
      intuition.
      subst.
      rewrite eqbPair_refl in H6.
      discriminate.

      simpl in *; intuition.
      subst.
      eapply comp_spec_eq_refl.

      eapply comp_spec_eq_refl.
      
    Qed.

    (* give the adversary a different random value *)
    Definition CtKDF_IND_CPA_G4 :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$
        compMap _
          (fun
             p => (@responseFunc _ _ _ _ _ _ (fst p) (snd p)))
          (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret false
      | Some lsR =>
        k <-$ rndRange; 
        k' <-$ rndRange;
        z1 <-$
        (
          A (snd (split lsSK)) (snd (split lsR)) k') _ _ 
          (fun s q => if (q ?= (format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR)))) then ret (k, (((format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR))), k)::s)) else randomFunc rndRange _ s q) nil;
          ret (fst z1)
      end.

    (* identical until bad argument. first expose bad event *)
    Definition CtKDF_IND_CPA_G3a :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$
        compMap _
          (fun
             p => (@responseFunc _ _ _ _ _ _ (fst p) (snd p)))
          (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret (false, false)
      | Some lsR =>
        k <-$ rndRange; 
        z1 <-$
        (
          A (snd (split lsSK)) (snd (split lsR)) k) _ _ 
          (fun s q => if (q ?= (format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR)))) then ret (k, (((format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR))), k)::s)) else randomFunc rndRange _ s q) nil;
          ret (fst z1, if (arrayLookup _ (snd z1) (format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR)))) then true else false )
      end.

    Theorem CtKDF_IND_CPA_G3a_equiv :
      Pr[CtKDF_IND_CPA_G3] == Pr[x <-$ CtKDF_IND_CPA_G3a; ret (fst x)].

      unfold CtKDF_IND_CPA_G3, CtKDF_IND_CPA_G3a.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      destOpt.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      reflexivity.
      fcf_simp.
      reflexivity.
    Qed.

    Ltac lookupMatch :=
      match goal with
      | [|- context [if (if ?a then _ else _) then _ else _ ] ] =>
        case_eq a; intros
      | [H: eqbPair _ _ _ _ = true |- _] =>
        apply eqbPair_prop in H; subst
      | [|- context[if ?a then _ else _] ] =>
        case_eq a; intros
      | [H1: arrayLookup _ ?a ?b = Some ?c, H2 : arrayLookup _ ?a ?b = None |- _ ] =>
        cut (None = Some c); try discriminate; rewrite <- H1; rewrite <- H2; reflexivity
      | [|- context[match ?a with | Some _ => _ | None => _ end] ] =>
        case_eq a; intros
      end.

    (* make the change *)
    Definition CtKDF_IND_CPA_G3b :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$
        compMap _
          (fun
             p => (@responseFunc _ _ _ _ _ _ (fst p) (snd p)))
          (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret (false, false)
      | Some lsR =>
        k <-$ rndRange; 
        k' <-$ rndRange;
        z1 <-$
        (
          A (snd (split lsSK)) (snd (split lsR)) k') _ _ 
          (fun s q => if (q ?= (format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR)))) then ret (k, (((format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR))), k)::s)) else randomFunc rndRange _ s q) nil;
          ret (fst z1, if (arrayLookup _ (snd z1) (format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR)))) then true else false )
      end.

    Definition CtKDF_IND_CPA_G3_bad :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$
        compMap _
          (fun
             p => (@responseFunc _ _ _ _ _ _ (fst p) (snd p)))
          (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret false
      | Some lsR =>
        k <-$ rndRange; 
        k' <-$ rndRange;
        z1 <-$
        (
          A (snd (split lsSK)) (snd (split lsR)) k') _ _ 
          (fun s q => if (q ?= (format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR)))) then ret (k, (((format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR))), k)::s)) else randomFunc rndRange _ s q) nil;
          ret (if (arrayLookup _ (snd z1) (format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR)))) then true else false )
      end.    

    Theorem CtKDF_IND_CPA_G3ab_bad_same : 
      Pr[x <-$ CtKDF_IND_CPA_G3a; ret (snd x)] == 
      Pr[x <-$ CtKDF_IND_CPA_G3b; ret (snd x)].

      eapply comp_spec_eq_impl_eq.

      unfold CtKDF_IND_CPA_G3a, CtKDF_IND_CPA_G3b.
      eapply (@comp_spec_seq _ _ (fun p1 p2 => snd p1 = snd p2)); eauto with inhabited.
   
      fcf_skip.
      fcf_skip.
      destOpt.
      fcf_swap rightc.
      fcf_skip.
      fcf_irr_r.
      eapply rndRange_wf.
      fcf_skip.
      eapply (@fcf_oracle_eq_until_bad _ _  
        (fun s => if (arrayLookup _ s (format context (snd (split b)) (snd (split l)),
          psk ++ flatten (fst (split l)))) then true else false)
        (fun s => if (arrayLookup _ s (format context (snd (split b)) (snd (split l)),
          psk ++ flatten (fst (split l)))) then true else false)
        (fun s1 s2 => 
              (forall x, x <> (format context (snd (split b)) (snd (split l)),
          psk ++ flatten (fst (split l))) -> arrayLookup _ s1 x = arrayLookup _ s2 x))
      ); intuition.

      (* wf *)
      lookupMatch.
      wftac.
      eapply randomFunc_wf; wftac.
      lookupMatch.
      wftac.
      eapply randomFunc_wf; wftac.

      simpl.
      lookupMatch.
      lookupMatch.
      eapply comp_spec_ret; intuition.
      simpl.
      rewrite eqbPair_refl.
      trivial.
      simpl.
      lookupMatch.
      lookupMatch.
      intuition.
      eauto.
      simpl in *.
      rewrite eqbPair_refl in *.
      discriminate.
      unfold randomFunc.
      rewrite H7.
      lookupMatch.
      eapply comp_spec_ret; intuition.
      fcf_skip.
      eapply comp_spec_ret; intuition.
      simpl.
      lookupMatch.
      trivial.
      eauto.
      simpl.
      lookupMatch.
      trivial.
      eauto.
      intuition; subst.
      rewrite eqbPair_refl in *.
      discriminate.

      case_eq (d
            ?= (format context (snd (split b))
                  (snd (split l)),
               psk ++ flatten (fst (split l)))); intros.
      rewrite H9 in H8.
      repeat simp_in_support.
      simpl in *.
      rewrite eqbPair_refl.
      trivial.
      rewrite H9 in H8.
      unfold randomFunc in *.
      match goal with
      | [H : In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H10 in H8.
      repeat simp_in_support.
      trivial.
      rewrite H10 in H8.
      repeat simp_in_support.
      simpl in *.
      rewrite eqbPair_symm.
      rewrite H9.
      lookupMatch.
      trivial.
      rewrite H8 in H7.
      discriminate.

      case_eq (d
            ?= (format context (snd (split b))
                  (snd (split l)),
               psk ++ flatten (fst (split l)))); intros.
      rewrite H9 in H8.
      repeat simp_in_support.
      simpl in *.
      rewrite eqbPair_refl.
      trivial.
      rewrite H9 in H8.
      unfold randomFunc in *.
      match goal with
      | [H : In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H10 in H8.
      repeat simp_in_support.
      trivial.
      rewrite H10 in H8.
      repeat simp_in_support.
      simpl in *.
      rewrite eqbPair_symm.
      rewrite H9.
      lookupMatch.
      trivial.
      rewrite H8 in H7.
      discriminate.

      simpl in *; intuition.
      eapply comp_spec_ret; intuition.
    
      eapply comp_spec_ret; intuition.

      intuition.
      simpl in *; subst.
      eapply comp_spec_eq_refl.

    Qed.

    Theorem CtKDF_IND_CPA_G3ab_eq_until_bad : forall a, 
      evalDist CtKDF_IND_CPA_G3a (a, false) ==
      evalDist CtKDF_IND_CPA_G3b (a, false).

      intuition.
      eapply comp_spec_impl_eq.

      unfold CtKDF_IND_CPA_G3a, CtKDF_IND_CPA_G3b.
      fcf_skip.
      fcf_skip.
      destOpt.
      fcf_swap rightc.
      fcf_skip.
      fcf_irr_r.
      eapply rndRange_wf.
      fcf_skip.

      eapply (@fcf_oracle_eq_until_bad _ _  
        (fun s => if (arrayLookup _ s (format context (snd (split b)) (snd (split l)),
          psk ++ flatten (fst (split l)))) then true else false)
        (fun s => if (arrayLookup _ s (format context (snd (split b)) (snd (split l)),
          psk ++ flatten (fst (split l)))) then true else false)
        (fun s1 s2 => 
              (forall x, x <> (format context (snd (split b)) (snd (split l)),
          psk ++ flatten (fst (split l))) -> arrayLookup _ s1 x = arrayLookup _ s2 x))
      ); intuition.

      (* wf *)
      lookupMatch.
      wftac.
      eapply randomFunc_wf; wftac.
      lookupMatch.
      wftac.
      eapply randomFunc_wf; wftac.

      simpl.
      lookupMatch.
      lookupMatch.
      eapply comp_spec_ret; intuition.
      simpl.
      rewrite eqbPair_refl.
      trivial.
      simpl.
      lookupMatch.
      lookupMatch.
      intuition.
      eauto.
      simpl in *.
      rewrite eqbPair_refl in *.
      discriminate.
      unfold randomFunc.
      rewrite H7.
      lookupMatch.
      eapply comp_spec_ret; intuition.
      fcf_skip.
      eapply comp_spec_ret; intuition.
      simpl.
      lookupMatch.
      trivial.
      eauto.
      simpl.
      lookupMatch.
      trivial.
      eauto.
      intuition; subst.
      rewrite eqbPair_refl in *.
      discriminate.

      case_eq (d
            ?= (format context (snd (split b))
                  (snd (split l)),
               psk ++ flatten (fst (split l)))); intros.
      rewrite H9 in H8.
      repeat simp_in_support.
      simpl in *.
      rewrite eqbPair_refl.
      trivial.
      rewrite H9 in H8.
      unfold randomFunc in *.
      match goal with
      | [H : In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H10 in H8.
      repeat simp_in_support.
      trivial.
      rewrite H10 in H8.
      repeat simp_in_support.
      simpl in *.
      rewrite eqbPair_symm.
      rewrite H9.
      lookupMatch.
      trivial.
      rewrite H8 in H7.
      discriminate.

      case_eq (d
            ?= (format context (snd (split b))
                  (snd (split l)),
               psk ++ flatten (fst (split l)))); intros.
      rewrite H9 in H8.
      repeat simp_in_support.
      simpl in *.
      rewrite eqbPair_refl.
      trivial.
      rewrite H9 in H8.
      unfold randomFunc in *.
      match goal with
      | [H : In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H10 in H8.
      repeat simp_in_support.
      trivial.
      rewrite H10 in H8.
      repeat simp_in_support.
      simpl in *.
      rewrite eqbPair_symm.
      rewrite H9.
      lookupMatch.
      trivial.
      rewrite H8 in H7.
      discriminate.

      simpl in *; intuition.
      eapply comp_spec_ret; intuition.
      pairInv.
      intuition.
      subst.
      rewrite H10.
      lookupMatch.
      reflexivity.
      reflexivity.

      pairInv.
      rewrite H10 in H11.
      intuition.
      subst.
      rewrite <- H10.
      lookupMatch.
      reflexivity.
      reflexivity.
      eapply comp_spec_ret; intuition idtac.
    Qed.

    Definition CtKDF_IND_CPA_G3_bad_equiv : 
      Pr[x <-$ CtKDF_IND_CPA_G3a; ret (snd x)] == Pr[CtKDF_IND_CPA_G3_bad].

      rewrite CtKDF_IND_CPA_G3ab_bad_same.
      unfold CtKDF_IND_CPA_G3b, CtKDF_IND_CPA_G3_bad.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      destOpt.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      reflexivity.
      fcf_simp.
      reflexivity.

    Qed.

    Theorem CtKDF_IND_CPA_G3ab_close : 
      | Pr[x <-$ CtKDF_IND_CPA_G3a; ret (fst x)] - Pr[x <-$ CtKDF_IND_CPA_G3b; ret (fst x)] | <=
      Pr[CtKDF_IND_CPA_G3_bad].

      eapply leRat_trans.
      eapply fundamental_lemma_h.
      eapply CtKDF_IND_CPA_G3ab_bad_same.
      eapply CtKDF_IND_CPA_G3ab_eq_until_bad.
      rewrite CtKDF_IND_CPA_G3_bad_equiv.
      reflexivity.
      
    Qed.

    Theorem CtKDF_IND_CPA_G3b_G4_equiv :
      Pr[x <-$ CtKDF_IND_CPA_G3b; ret (fst x)] == Pr[CtKDF_IND_CPA_G4].

      unfold CtKDF_IND_CPA_G3b, CtKDF_IND_CPA_G4.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      destOpt.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      reflexivity.
      fcf_simp.
      reflexivity.

    Qed.

    Theorem CtKDF_IND_CPA_G4_close : 
      | Pr[CtKDF_IND_CPA_G3] - Pr[CtKDF_IND_CPA_G4] | <=
      Pr[CtKDF_IND_CPA_G3_bad].

      rewrite CtKDF_IND_CPA_G3a_equiv.
      rewrite <- CtKDF_IND_CPA_G3b_G4_equiv.
      eapply CtKDF_IND_CPA_G3ab_close.

    Qed.

    (* use a regular random oracle *)
    Definition CtKDF_IND_CPA_G5 :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$
        compMap _
          (fun
             p => (@responseFunc _ _ _ _ _ _ (fst p) (snd p)))
          (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret false
      | Some lsR =>
        k <-$ rndRange;
        k' <-$ rndRange;
        z1 <-$
        (
          A (snd (split lsSK)) (snd (split lsR)) k') _ _ 
          (randomFunc rndRange _) ((((format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR))), k))::nil);
          ret (fst z1)
      end.

    Theorem CtKDF_IND_CPA_G5_equiv: 
      Pr [CtKDF_IND_CPA_G4] == Pr [CtKDF_IND_CPA_G5].

      symmetry.
      eapply comp_spec_eq_impl_eq.

      unfold CtKDF_IND_CPA_G4, CtKDF_IND_CPA_G5.
      simpl.
      fcf_skip.
      fcf_skip.
      destOpt.
      fcf_skip.
      fcf_skip.
      fcf_skip.
      eapply (@fcf_oracle_eq _ _
      (fun s1 s2 => 
      (arrayLookup _ s1 (format context (snd (split b)) (snd (split l)),
      psk ++ flatten (fst (split l))) = Some b1) /\
      forall x, (x <> (format context (snd (split b)) (snd (split l)),
      psk ++ flatten (fst (split l)))) -> arrayLookup _ s1 x = arrayLookup _ s2 x)
      ).
      intuition.
      simpl.
      rewrite eqbPair_refl.
      trivial.
      simpl.
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        case_eq a; intros
      end.
      apply eqbPair_prop in H9.
      subst.
      intuition.
      trivial.

      intuition.
      unfold randomFunc.  
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        case_eq a; intros
      end.
      apply eqbPair_prop in H8.
      subst.
      match goal with
      | [|- context[match ?a with | Some _ => _ | None => _ end] ] =>
        case_eq a; intros
      end.
      assert (Some l0 = Some b1).
      rewrite <- H8.
      rewrite <- H9.
      reflexivity.
      inversion H11; clear H11; subst.
      eapply comp_spec_ret; intuition.
      simpl.
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        case_eq a; intros
      end.
      apply eqbPair_prop in H12.
      intuition.
      eauto.
      assert (Some b1 = None).
      rewrite <- H8.
      rewrite <- H9.
      reflexivity.
      discriminate.

      rewrite H10.
      match goal with
      | [|- context[match ?a with | Some _ => _ | None => _ end] ] =>
        case_eq a; intros
      end.
      eapply comp_spec_ret; intuition.
      
      fcf_skip.
      eapply comp_spec_ret; intuition.
      simpl.
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        case_eq a; intros
      end.
      apply eqbPair_prop in H14.
      subst.
      rewrite eqbPair_refl in H8.
      discriminate.
      eauto.
      simpl.
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        case_eq a; intros
      end.
      trivial.
      eauto.
      intuition.
      subst.
      rewrite eqbPair_refl in H8.
      discriminate.

      simpl in *; intuition.
      subst.
      eapply comp_spec_eq_refl.
    
      eapply comp_spec_eq_refl.
      
    Qed.


    (* last game is equal to IND-CPA_G1 *)
    Theorem CtKDF_G5_IND_CPA_equiv: 
      Pr [CtKDF_IND_CPA_G5] ==
      Pr [ExpROM _ _ rndRange _ (KeyExchangeCPA_ROM_G1 rndRange A) ].

      Local Opaque evalDist.
      unfold CtKDF_IND_CPA_G5, ExpROM, KeyExchangeCPA_ROM_G1.
      simpl.
      fcf_inline_first.
      fcf_skip.
      reflexivity.
      fcf_simp.
      fcf_inline_first.
      fcf_simp.
      simpl.
      fcf_inline_first.
      fcf_skip.
      reflexivity.
      fcf_simp.
      fcf_inline_first.
      destOpt.
      simpl.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      fcf_inline_first.
      fcf_simp.
      simpl.
      fcf_inline_first.
      fcf_skip. 
      fcf_simp.
      fcf_skip.
      reflexivity.
      fcf_simp.
      reflexivity.

      simpl.
      fcf_inline_first.
      fcf_simp.
      simpl.
      fcf_inline_first.
      fcf_simp.
      reflexivity.

      Local Transparent evalDist.
    Qed.

    (* transform bad event to get adversary against OW-CPA *)
    (* simplify and use regular random oracle *)
    Definition CtKDF_IND_CPA_G3_bad_1 :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$
        compMap _
          (fun
             p => (@responseFunc _ _ _ _ _ _ (fst p) (snd p)))
          (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret false
      | Some lsR =>
        k' <-$ rndRange;
        z1 <-$
        (
          A (snd (split lsSK)) (snd (split lsR)) k') _ _ 
          (randomFunc rndRange _ ) nil;
          ret (if (arrayLookup _ (snd z1) (format context (snd (split lsSK)) (snd (split lsR)),
                psk ++ flatten (fst (split lsR)))) then true else false )
      end. 

    Theorem CtKDF_IND_CPA_G3_bad_1_equiv : 
      Pr[CtKDF_IND_CPA_G3_bad] == Pr[CtKDF_IND_CPA_G3_bad_1].
 
      eapply comp_spec_impl_eq.
  
      unfold CtKDF_IND_CPA_G3_bad, CtKDF_IND_CPA_G3_bad_1.
      fcf_skip.
      fcf_skip.
      destOpt.
      fcf_irr_l.
      eapply rndRange_wf.
      fcf_skip.
      fcf_skip.
      
      eapply (@fcf_oracle_eq_until_bad _ _  
        (fun s => if (arrayLookup _ s (format context (snd (split b)) (snd (split l)),
          psk ++ flatten (fst (split l)))) then true else false)
        (fun s => if (arrayLookup _ s (format context (snd (split b)) (snd (split l)),
          psk ++ flatten (fst (split l)))) then true else false)
        (fun s1 s2 => 
              (forall x, x <> (format context (snd (split b)) (snd (split l)),
          psk ++ flatten (fst (split l))) -> arrayLookup _ s1 x = arrayLookup _ s2 x))
      ); intuition.

      (* wf *)
      lookupMatch.
      wftac.
      eapply randomFunc_wf; wftac.
      eapply randomFunc_wf; wftac.

      simpl.
      unfold randomFunc.
      lookupMatch.
      lookupMatch.
      lookupMatch.
      eapply comp_spec_ret; intuition.
      simpl.
      rewrite eqbPair_refl.
      lookupMatch.
      trivial.
      lookupMatch.
      simpl in *.
      rewrite eqbPair_refl in *.
      discriminate.
      simpl in *.
      rewrite eqbPair_refl in *.
      discriminate.
      fcf_irr_r.
      eapply comp_spec_ret; intuition.
      simpl in *.
      rewrite eqbPair_refl.
      trivial.
      simpl in *.
    
      lookupMatch.
      lookupMatch.
      intuition.
      eauto.
      simpl in *.
      rewrite eqbPair_refl in *.
      discriminate.
      rewrite H7.
      lookupMatch.
      lookupMatch.
      assert (Some l0 = Some l1).
      rewrite <- H10. rewrite <- H11.
      reflexivity.
      inversion H12; clear H12; subst.
      eapply comp_spec_ret; intuition.
      lookupMatch.
      lookupMatch.
      lookupMatch.
      fcf_skip.
      eapply comp_spec_ret; intuition.
      simpl in *.
      lookupMatch.
      trivial.
      trivial.
      simpl in *.
      lookupMatch.
      trivial.
      eauto.
      intuition; subst.
      rewrite eqbPair_refl in *.
      discriminate.

      case_eq (d
            ?= (format context (snd (split b))
                  (snd (split l)),
               psk ++ flatten (fst (split l)))); intros.
      rewrite H9 in H8.
      repeat simp_in_support.
      simpl in *.
      rewrite eqbPair_refl.
      trivial.
      rewrite H9 in H8.
      unfold randomFunc in *.
      match goal with
      | [H : In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H10 in H8.
      repeat simp_in_support.
      trivial.
      rewrite H10 in H8.
      repeat simp_in_support.
      simpl in *.
      rewrite eqbPair_symm.
      rewrite H9.
      lookupMatch.
      trivial.
      rewrite H8 in H7.
      discriminate.

      simpl in *.
      unfold randomFunc in *.
      match goal with
      | [H : In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H9 in H8.
      repeat simp_in_support.
      trivial.
      rewrite H9 in H8.
      repeat simp_in_support.
      simpl in *.
      lookupMatch.
      trivial.
      lookupMatch.
      trivial.
      rewrite H11 in H7.
      discriminate.

      simpl in *; intuition.
      eapply comp_spec_ret; intuition.

      lookupMatch.
      trivial.
      match goal with
      | [H: (if ?a then _ else _ ) = (if ?b then _ else _) |- _] =>
        case_eq b; intros
      end.
      lookupMatch.
      rewrite H13 in H10.
      intuition.
      subst.
      match goal with
      | [H: context[(if ?a then _ else _ )] |- _] =>
        case_eq a; intros
      end.
      rewrite H14 in H10.
      discriminate.
      rewrite H14 in H9.
      discriminate.

      lookupMatch.
      trivial.
      rewrite H12 in H11.
      intuition.
      subst.
      rewrite H12 in H10.
      match goal with
      | [H: context[(if ?a then _ else _ )] |- _] =>
        case_eq a; intros
      end.
      rewrite H13 in H9.
      match goal with
      | [H: context[(if ?a then _ else _ )] |- _] =>
        case_eq a; intros
      end.
      rewrite H14 in H10.
      discriminate.
      lookupMatch.
      rewrite H13 in H9.
      discriminate.

      eapply comp_spec_ret; intuition.

    Qed.
      
    (* rearrange to run strong KE first *)
    Definition CtKDF_IND_CPA_G3_bad_2 :=
      SK_strong <-$ @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      R_strong <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) (snd SK_strong) );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1 <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2 <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match (stripOpt (lsR1 ++ R_strong :: lsR2)) with
      | None => ret false
      | Some lsR =>
        k' <-$ rndRange;
        z1 <-$
        (A (snd (split (lsSK1 ++ (SK_strong :: lsSK2)))) (snd (split lsR)) k') _ _ 
          (randomFunc rndRange _) nil;
          ret (if (arrayLookup _ (snd z1) (format context (snd (split (lsSK1 ++ (SK_strong :: lsSK2)))) (snd (split lsR)),
                psk ++ flatten (fst (split lsR)))) then true else false )
      end.

    Theorem CtKDF_IND_CPA_G3_bad_2_equiv : 
      Pr[CtKDF_IND_CPA_G3_bad_1] == Pr[CtKDF_IND_CPA_G3_bad_2].
  
      eapply CtKDF_SplitReorder_equiv; intuition.

    Qed.

    (* put in form of OW-CPA definition *)
    Definition strongKE_A P_strong R_strong :=
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match (stripOpt lsR1_opt) with
      | None => ret nil
      | Some lsR1 =>
        match (stripOpt lsR2_opt) with
        | None => ret nil
        | Some lsR2 =>
          k' <-$ rndRange;
          [_, s] <-$2 (A 
            (snd (split lsSK1) ++ (P_strong :: (snd (split lsSK2)))) 
            (snd (split lsR1) ++ (R_strong :: (snd (split lsR2)))) 
            k') _ _ (randomFunc rndRange _) nil;
          ret (fst (split s))
        end
      end.

    Definition CtKDF_IND_CPA_G3_bad_3 :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      match kR_opt with
      | None => ret false
      | Some (k, R) =>
        ls <-$ (strongKE_A P R);
        ret (any_dec ((fun q p => isSubListOf _ q (snd p)) k) ls)
      end.

    Theorem CtKDF_IND_CPA_G3_bad_3_equiv : 
      Pr[CtKDF_IND_CPA_G3_bad_2] <= Pr[CtKDF_IND_CPA_G3_bad_3].

      eapply comp_spec_impl_le.

      unfold CtKDF_IND_CPA_G3_bad_2, CtKDF_IND_CPA_G3_bad_3, strongKE_A.
      fcf_skip.
      fcf_simp.
      fcf_skip.
      fcf_simp.
      simpl.
      fcf_inline_first.
      destOpt.
      destruct p.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      rewrite stripOpt_app.
      case_eq (stripOpt b2); intros.
      simpl.
      case_eq (stripOpt b3); intros.
      simpl.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      fcf_inline_first.
      fcf_skip.
      repeat rewrite snd_split_app.
      simpl.
      remember (split b0) as z. destruct z.
      simpl.
      remember (split l0) as z. destruct z.
      simpl.
      reflexivity.

      fcf_inline_first.
      fcf_simp.
      simpl.
      eapply comp_spec_ret; intuition.
      pairInv.
      
      rewrite arrayLookup_any_dec_eq in H18.
      apply any_dec_true_ex in H18.
      destruct H18.
      intuition.
      simpl in *.
      apply eqbPair_prop in H19.
      subst.
      destruct x; simpl in *.
      subst.
      eapply any_dec_true_ex.
      econstructor.
      intuition.
      eapply in_split_l.
      eauto.
      simpl.
      repeat rewrite fst_split_app in *.
      repeat rewrite fst_split_cons in *.
      simpl.
      eapply isSubListOf_app. 
      eapply orb_true_intro.
      right.
      rewrite flatten_app.
      eapply isSubListOf_app.
      eapply orb_true_intro.
      right.
      simpl.
      eapply isSubListOf_app.
      eapply orb_true_intro.
      left.
      eapply isSubListOf_refl.

      simpl.
      fcf_simp.
      eapply comp_spec_ret; intuition.
      
      simpl.
      fcf_simp.
      eapply comp_spec_ret; intuition.

      subst.
      simpl in *.
      fcf_irr_l.
      eapply compMap_wf; intros.
      eapply keyGen_wf.
      eapply firstn_In; eauto.
      fcf_irr_l.
      eapply compMap_wf; intros.
      eapply keyGen_wf.
      destruct KE; trivial.
      simpl. right.
      eapply skipn_In; eauto.
      fcf_irr_l.
      eapply compMap_wf; intros.
      eapply responseFunc_wf.
      destruct a2; simpl in *.
      eapply firstn_In.
      eapply in_combine_l; eauto.
      fcf_irr_l.
      eapply compMap_wf; intros.
      destruct KE; simpl in *; intuition idtac.
      eapply responseFunc_wf. right.
      destruct a3; simpl in *.
      eapply skipn_In.
      eapply in_combine_l; eauto.
      
      rewrite stripOpt_app.
      destruct (stripOpt a2);
      simpl.
      eapply comp_spec_ret; intuition.
      eapply comp_spec_ret; intuition.
     
    Qed.

    Theorem CtKDF_IND_CPA_G3_bad_3_OW_CPA_equiv : 
      Pr[CtKDF_IND_CPA_G3_bad_3] == 
      (@KeyExchangeOW_CPA_List_Advantage _ _ _ _ _ _ _ (nth strongKE KE defKE) (fun q p => isSubListOf _ q (snd p)) strongKE_A).

      reflexivity.

    Qed.

    Theorem CtKDF_IND_CPA_secure : 
      KeyExchangeCPA_O_Advantage (rndOctetString keyLength) A _ _ (rndOctetString keyLength) <= 
      (@KeyExchangeOW_CPA_List_Advantage _ _ _ _ _ _ _ (nth strongKE KE defKE) (fun q p => isSubListOf _ q (snd p)) strongKE_A).

      unfold KeyExchangeCPA_O_Advantage. 
      rewrite CtKDF_IND_CPA_G1_equiv.
      rewrite CtKDF_IND_CPA_G2_equiv.
      rewrite CtKDF_IND_CPA_G3_equiv.
      rewrite <- CtKDF_G5_IND_CPA_equiv.
      rewrite <- CtKDF_IND_CPA_G5_equiv.  
      rewrite CtKDF_IND_CPA_G4_close.
      rewrite CtKDF_IND_CPA_G3_bad_1_equiv.
      rewrite CtKDF_IND_CPA_G3_bad_2_equiv.
      rewrite CtKDF_IND_CPA_G3_bad_3_equiv.
      rewrite CtKDF_IND_CPA_G3_bad_3_OW_CPA_equiv.
      reflexivity.
    Qed.

  End CtKDF_IND_CPA_ROM.

End CtKDF_ROM.


