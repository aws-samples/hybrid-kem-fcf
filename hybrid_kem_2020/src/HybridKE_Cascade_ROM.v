(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: MIT-0 *)

Require Import FCF.
Require Import FCF.CompFold.
Require Import FCF.OracleCompFold.
Require Import FCF.PRF.
Require Import FCF.ROM.
Require Import FCF.RndListPred.
Require Import Permutation.

Require Import KeyExchange.
Require Import KeyExchange_ROM.
Require Import HybridKE.
Require Import HybridKE_ROM.

Set Implicit Arguments.

(* A list of random values, with later values added to the front of the list.
This is needed in this proof because the normal method compMap puts later
values at the end of the list. *)
Section RndList.

  Variable A : Set.
  Hypothesis eqda : EqDec A.
  Variable c : Comp A.
  Hypothesis c_wf : well_formed_comp c.

  Fixpoint rndList(n : nat) :=
    match n with
    | 0 => ret nil
    | S n' => a <-$ c; ls <-$ rndList n'; ret ls ++ (a :: nil)
    end.

  Theorem rndList_wf : forall (n : nat),
    well_formed_comp (rndList n).

    induction n; intuition; simpl in *;
    wftac.
  Qed.

  Theorem rndList_tl_eq : forall (n : nat),
    comp_spec (fun a b => tl a = b)
      (rndList (S n))
      (rndList n).

    induction n; intuition; simpl in *.
    fcf_irr_l.
    fcf_simp.
    eapply comp_spec_ret; intuition.

    fcf_skip.
    fcf_skip.
    eauto.
    eapply comp_spec_ret; intuition.
    subst.  
    apply tl_app_eq.
    repeat simp_in_support.
    eapply app_cons_not_nil.
    eauto.

  Qed.

  Theorem rndList_length : forall n a,
    In a (getSupport (rndList n)) ->
    length a = n.

    induction n; intuition.
    simpl in *.
    intuition; subst.
    trivial.

    unfold rndList in *.
    fold rndList in *.
    repeat simp_in_support.
    eapply IHn in H1.
    subst.
    rewrite app_length.
    simpl.
    lia.

  Qed.

  Theorem rndList_map_perm : 
    forall (n : nat),
    comp_spec (@Permutation A)
    (rndList n)
    (compMap _
     (fun _ : nat => c)
     (forNats n)).

    induction n; intuition; simpl in *.
    eapply comp_spec_ret; intuition.
    fcf_skip.
    fcf_skip.
    eauto.
    eapply comp_spec_ret; intuition.
    eapply Permutation_trans.
    eapply Permutation_app_comm.
    simpl.
    econstructor.
    trivial.
 
  Qed.

End RndList.

Definition first(A : Type)(ls : list A) :=
  firstn (pred (length ls)) ls.

Ltac destOpt := 
  match goal with
  | [ |- context[match ?a with | Some _ => _ | None => _ end] ] =>
    case_eq a; intros
  end.

Section CasKDF_ROM.

  Variable digestLen secretLen: nat.
  Variable psk : OctetString.
  (* different context and label for each KE *)
  Variable context : list OctetString.
  (* Model the KDF for each length as a RO with range of the correct length. *)

  (* the "full" context for a KE is the transcript of public values plus the fixed context+label for that KE *)
  Definition FullContext := (OctetString * OctetString * OctetString)%type.
  (* The domain is full context * (psk * secret) *)
  Definition DomainRO := (FullContext * (OctetString * OctetString))%type.
  (* values in range have length keyLength *)
  Definition RangeRO := OctetString. 
  Definition rndRange := rndOctetString (digestLen + secretLen).

  Definition kdf := (@randomFunc DomainRO _ (rndRange) _).
  
  (* casKDF returns the entire list of secrets, but only the last one is secure *)
  Fixpoint casKDF cs ps : OracleComp DomainRO RangeRO (list OctetString) :=
    match ps with
    | nil => $ret nil
    | (k, ctxt) :: ps' =>
      ks <--$ query (ctxt, (k, cs));
      ls <--$ casKDF (firstn digestLen ks) ps';
      $ret (skipn digestLen ks) :: ls
    end.

  Theorem casKDF_cons : forall p1 p2 cs (S : Set)(eqds : EqDec S) o (s : S) x,
    evalDist ((casKDF cs (p1 :: p2)) _ _ o s) x == 
    evalDist ((ks <--$ query (snd p1, (fst p1, cs)); ls <--$ casKDF (firstn digestLen ks) p2; $ret (skipn digestLen ks)::ls) _ _ o s) x.
  
    intros.
    simpl.
    destruct p1.
    simpl.
    reflexivity.

  Qed.

  Fixpoint casKDF_cs cs ps : OracleComp DomainRO RangeRO (OctetString * (list OctetString)) :=
    match ps with
    | nil => $ret (cs, nil)
    | (k, ctxt) :: ps' =>
      ks <--$ query (ctxt, (k, cs));
      [cs', ls] <--$2 casKDF_cs (firstn digestLen ks) ps';
      $ret (cs', ((skipn digestLen ks) :: ls))
    end.

  Theorem casKDF_app : forall p1 p2 cs (S : Set)(eqds : EqDec S) o (s : S) x,
    evalDist ((casKDF cs (p1 ++ p2)) _ _ o s) x == 
    evalDist (([cs', ls] <--$2 casKDF_cs cs p1; ls' <--$ casKDF cs' p2; $ret (ls ++ ls')) _ _ o s) x.

    Local Opaque evalDist.

    induction p1; intuition; simpl in *.
    fcf_inline_first.
    fcf_simp.
    rewrite <- evalDist_right_ident.
    fcf_skip.
    reflexivity.
    fcf_simp.
    simpl.
    eapply evalDist_ret_eq.
    reflexivity.

    fcf_inline_first.
    fcf_skip.
    reflexivity.
    fcf_simp.
    eapply eqRat_trans.
    eapply (evalDist_seq_eq _ _ _
    (fun x => ([z, s']<-2 x;
   x0 <-$ ret skipn digestLen l :: z; ret (x0, s')))
    ).
    eauto.
    intros.
    fcf_simp.
    eapply evalDist_ret_eq.
    reflexivity.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    simpl.
    fcf_inline_first.
    fcf_simp.
    simpl.
    fcf_skip.
    fcf_simp.
    fcf_inline_first.
    eapply evalDist_ret_eq.
    reflexivity.

    Unshelve.
    eauto with typeclass_instances.

    Local Transparent evalDist.

  Qed.

  Theorem casKDF_app_spec : forall p1 p2 cs (S : Set)(eqds : EqDec S) o (s : S),
    comp_spec eq 
      ((casKDF cs (p1 ++ p2)) _ _ o s)
      (([cs', ls] <--$2 casKDF_cs cs p1; ls' <--$ casKDF cs' p2; $ret (ls ++ ls')) _ _ o s).

    intuition.
    eapply eq_impl_comp_spec_eq.
    intros.
    eapply casKDF_app.
  Qed.
  
  Definition OctetStringKE := (@KeyExchange OctetString OctetString OctetString OctetString _ _ ).
  Variable KE : list OctetStringKE.
  Variable defKE : OctetStringKE.
  Hypothesis KE_nz : length KE <> O.

  Hypothesis keyGen_wf : forall ke, 
    In ke KE -> well_formed_comp (@keyGen _ _ _ _ _ _ ke).

  Hypothesis responseFunc_wf : forall ke P, 
    In ke KE -> well_formed_comp (@responseFunc _ _ _ _ _ _ ke P).
  
  Hypothesis context_length : length context = length KE.

  Definition casKeyGen (KE : list OctetStringKE) : OracleComp DomainRO RangeRO (list OctetString * list OctetString) :=
    ls <--$$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE; 
    $ret (fst (split ls), snd (split ls)).

  (* The cascade response func returns all secret keys except for the last as auxiliary information.*)
  Definition casResponseFunc (KE : list OctetStringKE)(Ps : list OctetString) : OracleComp DomainRO RangeRO (option (OctetString * (list OctetString * list OctetString))) :=
    ls_opt <--$$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE Ps);
    match (stripOpt ls_opt) with
    | None => $ret None
    | Some ls =>
      Rs <- snd (split ls); 
      k <--$ casKDF psk (combine (fst (split ls)) (combine (combine Ps Rs) context));
      k_first <- first k;
      k_last <- last k nil;
      $ret Some (k_last, (k_first, Rs))
    end.

  Instance CasKE : (@KeyExchange_ROM (list OctetString) (list OctetString) (list OctetString * list OctetString) OctetString DomainRO RangeRO _ _ ) := {
    keyGen_ROM := casKeyGen KE;
    responseFunc_ROM := casResponseFunc KE
  }.
    
  (* assume an arbitrary "strong" KE scheme *)
  Variable strongKE : nat.
  Hypothesis strongKE_small : strongKE < length KE.

  Section CasKDF_IND_CPA_ROM.

    Definition rndSharedSecret := rndOctetString secretLen.

    Variable A : (list OctetString) -> (list OctetString * list OctetString) -> OctetString -> OracleComp DomainRO RangeRO bool.
    Hypothesis A_wf : forall x y z, well_formed_oc (A x y z).
    Variable q : nat.
    Hypothesis A_qam : forall a b c, queries_at_most (A a b c) q.

   (* Before we extract the last value from the cascade and replace it with a random value, we
      1) Split out the "strong" KE scheme and reorder so it happens first
      2) Split the cascade into three parts
      3) Modify each part of the cascade so that it uses independent random values (+ collision bound)

    Then we put everything back after extracting a random value. So we need a reusable argument to
    make this modification twice. We accomplish this by making a new section to generalize the adversary.
    *)

    Theorem rndOctetString_wf : forall n,
      well_formed_comp (rndOctetString n).

      intuition.
      eapply compMap_wf.
      intuition.
      unfold rndOctet.
      wftac.
    Qed.

    Theorem CasKDF_wf : forall ls k,
      well_formed_oc (casKDF k ls).

      induction ls; intuition; simpl in *;
      wftac.

    Qed.

    Hint Resolve CasKDF_wf : wf.

    Theorem rndRange_wf : well_formed_comp rndRange.

      unfold rndRange.
      eapply compMap_wf.
      intuition.
      unfold rndOctet.
      wftac.

    Qed.

    Hint Resolve rndRange_wf : wf.

    Section CasKDF_SplitReorder.

    Variable B : (list OctetString) -> (list OctetString * list OctetString) -> OctetString -> OracleComp DomainRO RangeRO bool.
    Hypothesis B_wf : forall x y z, well_formed_oc (B x y z).

    (* unfold definitions and simplify *)
    Definition CasKDF_IND_CPA_G1 :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret false
      | Some lsR =>
        [sk, Ps] <-2 (fst (split lsSK), snd (split lsSK));
        [ks, Rs] <-2 (fst (split lsR), snd (split lsR));
        [k, st] <-$2 (casKDF psk (combine ks (combine (combine Ps Rs) context)))  _ _ (randomFunc rndRange _) nil;
        [b, _] <-$2 (B Ps ((first k), Rs) (last k nil)) _ _ (randomFunc rndRange _) st;
        ret b
      end.

    (* use a random value for each iteration of the cascade. This is the same unless there is a collision.*)
    Definition CasKDF_IND_CPA_G2 :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret false
      | Some lsR =>
        [sk, Ps] <-2 (fst (split lsSK), snd (split lsSK));
        [ks, Rs] <-2 (fst (split lsR), snd (split lsR));
        [k, st] <-$2 (casKDF psk (combine ks (combine (combine Ps Rs) context)))  _ _ (rndHist _ _ rndRange) nil;
        [b, _] <-$2 (B Ps (first k, Rs) (last k nil)) _ _ (randomFunc rndRange _) st;
        ret b
      end.

    Definition CasKDF_IND_CPA_G1a :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret false
      | Some lsR =>
        [sk, Ps] <-2 (fst (split lsSK), snd (split lsSK));
        [ks, Rs] <-2 (fst (split lsR), snd (split lsR));
        [k, st] <-$2 (casKDF psk (combine ks (combine (combine Ps Rs) context)))  _ _ (randomFunc_hist _ _ rndRange) nil;
        [b, _] <-$2 (B Ps (first k, Rs) (last k nil)) _ _ (randomFunc rndRange _) st;
        ret b
      end.

    Theorem CasKDF_IND_CPA_G1a_equiv : 
      Pr[CasKDF_IND_CPA_G1] == Pr[CasKDF_IND_CPA_G1a].
  
      eapply comp_spec_eq_impl_eq.
      unfold CasKDF_IND_CPA_G1, CasKDF_IND_CPA_G1a.
      fcf_skip.
      fcf_skip.
      destOpt.
      fcf_skip.
      eapply (fcf_oracle_eq (lookupEq _)).
      unfold lookupEq; intuition.
      intuition.  
      eapply randomFunc_hist_spec.
      trivial.
      fcf_simp.

      intuition; simpl in *; subst.
      fcf_skip.
      eapply (fcf_oracle_eq (lookupEq _)).
      trivial.
      intuition.
      eapply randomFunc_lookupEq_spec.
      trivial.
      fcf_simp.

      intuition; simpl in *; subst.
      eapply comp_spec_eq_refl.
      eapply comp_spec_eq_refl.

    Qed.

    Definition CasKDF_IND_CPA_G1b :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret (false, false)
      | Some lsR =>
        [sk, Ps] <-2 (fst (split lsSK), snd (split lsSK));
        [ks, Rs] <-2 (fst (split lsR), snd (split lsR));
        [k, st] <-$2 (casKDF psk (combine ks (combine (combine Ps Rs) context)))  _ _ (randomFunc_hist _ _ rndRange) nil;
        [b, _] <-$2 (B Ps (first k, Rs) (last k nil)) _ _ (randomFunc rndRange _) st;
        ret (b, hasDup _ (fst (split st)))
      end.

    Theorem CasKDF_IND_CPA_G1b_equiv : 
      Pr[CasKDF_IND_CPA_G1a] == Pr[x <-$ CasKDF_IND_CPA_G1b; ret (fst x)].

      unfold CasKDF_IND_CPA_G1a, CasKDF_IND_CPA_G1b.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      destOpt.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      reflexivity.
    
      fcf_simp.
      reflexivity.

    Qed.

    Definition CasKDF_IND_CPA_G1c :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret (false, false)
      | Some lsR =>
        [sk, Ps] <-2 (fst (split lsSK), snd (split lsSK));
        [ks, Rs] <-2 (fst (split lsR), snd (split lsR));
        [k, st] <-$2 (casKDF psk (combine ks (combine (combine Ps Rs) context)))  _ _ (rndHist _ _ rndRange) nil;
        [b, _] <-$2 (B Ps (first k, Rs) (last k nil)) _ _ (randomFunc rndRange _) st;
        ret (b, hasDup _ (fst (split st)))
      end.

    Theorem CasKDF_IND_CPA_G1bc_bad_eq : 
      Pr[x <-$ CasKDF_IND_CPA_G1b; ret (snd x)] == Pr[x <-$ CasKDF_IND_CPA_G1c; ret (snd x)].
    
      eapply comp_spec_impl_eq.
      unfold CasKDF_IND_CPA_G1b, CasKDF_IND_CPA_G1c.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      destOpt.
      fcf_inline_first.
      fcf_skip.
      eapply (fcf_oracle_eq_until_bad
        (fun s => hasDup _ (fst (split s)))
        (fun s => hasDup _ (fst (split s)))
        eq
      ).
      wftac.
      intuition.
      eapply randomFunc_hist_wf.
      wftac.
      intuition.
      eapply rndHist_wf.
      intuition.

      intuition.
      unfold randomFunc_hist, rndHist.
      match goal with
      | [|- context[match ?a with | Some _ => _ | None => _ end] ] =>
        case_eq a; intros
      end.
      fcf_irr_r.
      fcf_simp.
      eapply comp_spec_ret; intuition; subst.
      simpl.
      destruct (split x2).
      reflexivity.
      simpl in *.
      remember (split x2) as z. destruct z.
      simpl in *.
      apply arrayLookup_Some_impl_In in H6.
      eapply in_split_l in H6.
      simpl in *.
      rewrite <- Heqz in H6.
      simpl in *.
      match goal with
      | [H: context[if ?a then _ else _] |- _] =>
        destruct a; intros
      end.
      discriminate.

      intuition.
      simpl in *.
      remember (split x2) as z. destruct z.
      simpl in *.
      match goal with
      | [H: context[if ?a then _ else _] |- _] =>
        destruct a; intros
      end.
      discriminate.
      apply arrayLookup_Some_impl_In in H6.
      eapply in_split_l in H6.
      simpl in *.
      rewrite <- Heqz in H6.
      simpl in *.
      intuition.

      fcf_skip.
      eapply comp_spec_ret; intuition.

      intuition.
      unfold randomFunc_hist in *.
      match goal with
      | [H: context[match ?a with | Some _ => _ | None => _ end] |- _] =>
        case_eq a; intros
      end.
      rewrite H6 in H5.
      repeat simp_in_support.
      simpl.
      remember (split c0) as z. destruct z.
      simpl.
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        destruct a
      end; trivial.

      rewrite H6 in H5.
      repeat simp_in_support.
      simpl.
      remember (split c0) as z. destruct z.
      simpl.
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        destruct a
      end; trivial.

      intuition.
      unfold rndHist in *.
      repeat simp_in_support.
      simpl.
      remember (split c0) as z. destruct z.
      simpl.
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        destruct a
      end; trivial.
      trivial.
      reflexivity.

      simpl in *; intuition.
      case_eq (hasDup
       (pair_EqDec
          (pair_EqDec
             (pair_EqDec (list_EqDec (Bvector_EqDec 8))
                (list_EqDec (Bvector_EqDec 8)))
             (list_EqDec (Bvector_EqDec 8)))
          (pair_EqDec (list_EqDec (Bvector_EqDec 8))
             (list_EqDec (Bvector_EqDec 8)))) 
       (fst (split b1))); intros.
      fcf_simp.
      fcf_inline_first.
      fcf_irr_l.
      unfold DomainRO, FullContext, OctetString, Octet.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply list_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply oc_comp_wf.
      eapply B_wf.
      intuition.
      eapply randomFunc_wf.
      wftac.
      fcf_irr_r.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply list_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply oc_comp_wf.
      eapply B_wf.
      intuition.
      eapply randomFunc_wf.
      wftac.
      fcf_simp.
      eapply comp_spec_ret; intuition.
      simpl in *.
      rewrite <- H7.
      trivial.

      intuition; simpl in *; subst.
      fcf_simp.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      eapply comp_spec_ret; intuition.

      fcf_simp.
      eapply comp_spec_ret; intuition.
     
    Qed.

    Theorem CasKDF_IND_CPA_G1bc_eq_until_bad : forall x, 
      evalDist CasKDF_IND_CPA_G1b (x, false) == evalDist CasKDF_IND_CPA_G1c (x, false).
  
      intuition.
      eapply comp_spec_impl_eq.
      unfold CasKDF_IND_CPA_G1b, CasKDF_IND_CPA_G1c.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      destOpt.
      fcf_inline_first.
      fcf_skip.
      eapply (fcf_oracle_eq_until_bad
        (fun s => hasDup _ (fst (split s)))
        (fun s => hasDup _ (fst (split s)))
        eq
      ).
      wftac.
      intuition.
      eapply randomFunc_hist_wf.
      wftac.
      intuition.
      eapply rndHist_wf.
      wftac.
      intuition.
      unfold randomFunc_hist, rndHist.
      match goal with
      | [|- context[match ?a with | Some _ => _ | None => _ end] ] =>
        case_eq a; intros
      end.
      fcf_irr_r.
      fcf_simp.
      eapply comp_spec_ret; intuition; subst.
      simpl.
      destruct (split x2).
      reflexivity.
      simpl in *.
      remember (split x2) as z. destruct z.
      simpl in *.
      apply arrayLookup_Some_impl_In in H6.
      eapply in_split_l in H6.
      simpl in *.
      rewrite <- Heqz in H6.
      simpl in *.
      match goal with
      | [H: context[if ?a then _ else _] |- _] =>
        destruct a; intros
      end.
      discriminate.

      intuition.
      simpl in *.
      remember (split x2) as z. destruct z.
      simpl in *.
      match goal with
      | [H: context[if ?a then _ else _] |- _] =>
        destruct a; intros
      end.
      discriminate.
      apply arrayLookup_Some_impl_In in H6.
      eapply in_split_l in H6.
      simpl in *.
      rewrite <- Heqz in H6.
      simpl in *.
      intuition.

      fcf_skip.
      eapply comp_spec_ret; intuition.

      intuition.
      unfold randomFunc_hist in *.
      match goal with
      | [H: context[match ?a with | Some _ => _ | None => _ end] |- _] =>
        case_eq a; intros
      end.
      rewrite H6 in H5.
      repeat simp_in_support.
      simpl.
      remember (split c0) as z. destruct z.
      simpl.
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        destruct a
      end; trivial.

      rewrite H6 in H5.
      repeat simp_in_support.
      simpl.
      remember (split c0) as z. destruct z.
      simpl.
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        destruct a
      end; trivial.

      intuition.
      unfold rndHist in *.
      repeat simp_in_support.
      simpl.
      remember (split c0) as z. destruct z.
      simpl.
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        destruct a
      end; trivial.
      trivial.
      reflexivity.

      simpl in *; intuition.
      case_eq (hasDup
       (pair_EqDec
          (pair_EqDec
             (pair_EqDec (list_EqDec (Bvector_EqDec 8))
                (list_EqDec (Bvector_EqDec 8)))
             (list_EqDec (Bvector_EqDec 8)))
          (pair_EqDec (list_EqDec (Bvector_EqDec 8))
             (list_EqDec (Bvector_EqDec 8)))) 
       (fst (split b1))); intros.
      fcf_simp.
      fcf_inline_first.
      fcf_irr_l.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply list_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply oc_comp_wf.
      eapply B_wf.
      intuition.
      eapply randomFunc_wf.
      wftac.
      fcf_irr_r.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply list_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply oc_comp_wf.
      eapply B_wf.
      intuition.
      eapply randomFunc_wf.
      wftac.
      fcf_simp.
      eapply comp_spec_ret; intuition.
      pairInv.
      assert (true = false).
      rewrite <- H14.
      rewrite <- H6.
      reflexivity.
      discriminate.
      pairInv.
      assert (true = false).
      rewrite <- H14.
      rewrite <- H6.
      simpl in *.
      rewrite <- H7.
      reflexivity.
      discriminate.

      intuition; simpl in *; subst.
      fcf_simp.
      fcf_inline_first.
      fcf_skip.
      eapply comp_spec_ret; intuition.

      eapply comp_spec_ret; intuition.

    Qed.

    Theorem CasKDF_IND_CPA_G1bc_close : 
      | Pr[x <-$ CasKDF_IND_CPA_G1b; ret (fst x)] - Pr[x <-$ CasKDF_IND_CPA_G1c; ret (fst x)] | <= 
      Pr[x <-$ CasKDF_IND_CPA_G1b; ret (snd x)].

      eapply fundamental_lemma_h.
      eapply CasKDF_IND_CPA_G1bc_bad_eq.
      eapply CasKDF_IND_CPA_G1bc_eq_until_bad.

    Qed.

    Definition CasKDF_IND_CPA_G1_bad1 :=
      lsSK <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) KE;
      lsR_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine KE (snd (split lsSK)));
      match (stripOpt lsR_opt) with
      | None => ret false
      | Some lsR =>
        [sk, Ps] <-2 (fst (split lsSK), snd (split lsSK));
        [ks, Rs] <-2 (fst (split lsR), snd (split lsR));
        [_, st] <-$2 (casKDF psk (combine ks (combine (combine Ps Rs) context)))  _ _ (rndHist _ _ rndRange) nil;
        ret (hasDup _ (fst (split st)))
      end.

    Theorem CasKDF_IND_CPA_G1_bad1_equiv : 
      Pr[x <-$ CasKDF_IND_CPA_G1c; ret (snd x)] == Pr[CasKDF_IND_CPA_G1_bad1].

      unfold CasKDF_IND_CPA_G1c, CasKDF_IND_CPA_G1_bad1.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      destOpt.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      fcf_inline_first.
      fcf_irr_l.
      eapply oc_comp_wf.
      eapply B_wf.
      intuition.
      eapply randomFunc_wf.
      wftac.
      fcf_simp.
      reflexivity.

      fcf_simp.
      reflexivity.

    Qed.

    Definition CasKDF_IND_CPA_G1_bad2 :=
      s2 <-$ rndList _ (rndOctetString digestLen) (length KE);
      ret (hasDup _ (tl (s2 ++ psk :: nil))).

    Theorem forNats_list_pred_app : forall n1 n2,
      list_pred (fun a b => True) 
        (forNats (n1 + n2))
        (forNats n1 ++ forNats n2).

      intuition.
      eapply list_pred_I.
      rewrite app_length.
      repeat rewrite forNats_length.
      trivial.

    Qed.
  
    Theorem rndRange_split : 
      comp_spec eq rndRange
    (compMap (Bvector_EqDec 8)
      (fun _ : nat => rndOctet)
      (forNats digestLen ++ forNats secretLen)).

      unfold rndRange, rndOctetString.
      eapply eq_impl_comp_spec_eq.
      intros.
      eapply (@compMap_eq _ _ (fun a b => True)).
      eapply forNats_list_pred_app.
      intuition.
      
    Qed. 

    Theorem rndRange_firstn_spec : 
      comp_spec (fun a b => firstn digestLen a = b)
      rndRange (rndOctetString digestLen).

      unfold rndRange, rndOctetString.
      eapply comp_spec_eq_trans_l.
      eapply rndRange_split.
      eapply comp_spec_eq_trans_l.
      eapply eq_impl_comp_spec_eq.
      eapply compMap_app.
      eapply comp_spec_eq_trans_r.
      2:{
      eapply comp_spec_right_ident.
      }
      fcf_skip.
      fcf_irr_l.
      eapply compMap_wf.
      intuition.
      unfold rndOctet.
      wftac.
      eapply comp_spec_ret; intuition.
      apply compMap_length in H0.
      rewrite forNats_length in H0.
      rewrite <- H0.
      rewrite firstn_app.
      rewrite minus_diag.
      simpl.
      rewrite firstn_all.
      apply app_nil_r.
    Qed.

    Theorem rndRange_skipn_spec : 
      comp_spec (fun a b => skipn digestLen a = b)
      rndRange (rndOctetString secretLen).

      unfold rndRange, rndOctetString.
      eapply comp_spec_eq_trans_l.
      eapply rndRange_split.
      eapply comp_spec_eq_trans_l.
      eapply eq_impl_comp_spec_eq.
      eapply compMap_app.
      eapply comp_spec_eq_trans_r.
      2:{
      eapply comp_spec_right_ident.
      }
      fcf_irr_l.
      eapply compMap_wf.
      intuition.
      unfold rndOctet.
      wftac.
      fcf_skip.
      eapply comp_spec_ret; intuition.
      apply compMap_length in H.
      rewrite forNats_length in H.
      rewrite <- H.
      rewrite skipn_app.
      trivial.

    Qed.

    Theorem firstn_0 : forall (A : Type)(ls : list A),
      firstn 0 ls = nil.

      intuition.

    Qed.

    Theorem firstn_S_app : forall(A : Type) (b1 : list A) n,
      firstn (S n) b1 = (firstn n b1) ++ (firstn 1 (skipn n b1)).

      induction b1; intuition; simpl in *.
      rewrite firstn_nil.
      rewrite skipn_nil.
      reflexivity.
      destruct n; simpl in *.
      trivial.
      f_equal.
      eauto.

    Qed.

    Theorem casKDF_rndHist_rndRange_spec : forall n ls1 k ls2 eqd1 eqd2 eqd3 eqd4,
      length ls1 = n ->
      comp_spec (fun a b => skipn n (snd a) = ls2 /\ Forall2 (fun x y => (snd x) = y) (firstn n (snd a)) b)
      ((casKDF k ls1) _ eqd1 (rndHist eqd2 eqd3 rndRange) ls2)
      (rndList eqd4 rndRange n).

      Local Opaque firstn skipn.

      induction n; destruct ls1; intuition; simpl in *.
      fcf_simp.
      eapply comp_spec_ret; intuition.

      lia.
      lia.
      
      unfold rndHist.
      fcf_inline_first.
      fcf_skip.
      fcf_skip.
      eapply IHn.
      lia.
      eapply comp_spec_ret; intuition.
      simpl in *.
      intuition.
      rewrite <- tl_skipn_eq.
      rewrite H5.
      reflexivity.
      simpl in *.
      intuition.
      assert ((firstn (S n) b1) = 
        (firstn n b1 ++ (firstn 1 (skipn n b1)))).
      eapply firstn_S_app.
      rewrite H4.
      eapply Forall2_app.
      trivial.
      rewrite H5.
    
      Local Transparent firstn skipn.
      simpl.
      econstructor.
      trivial.
      econstructor.
    Qed.

    Theorem casKDF_rndHist_rndOctetString_spec : forall n ls1 k ls2,
      length ls1 = n ->
      comp_spec (fun a b => skipn n (snd a) = ls2 /\ Forall2 (fun x y => (firstn digestLen (snd x)) = y) (firstn n (snd a)) b)
      ((casKDF k ls1) _ _ (rndHist _ _ rndRange) ls2)
      (rndList _ (rndOctetString digestLen) n).

      Local Opaque firstn skipn.

      induction n; destruct ls1; intuition; simpl in *.
      fcf_simp.
      eapply comp_spec_ret; intuition.

      lia.
      lia.
      
      unfold rndHist.
      fcf_inline_first.
      fcf_skip.
      eapply rndRange_firstn_spec.
      fcf_skip.
      eapply comp_spec_ret; intuition.
      simpl in *.
      rewrite <- tl_skipn_eq.
      rewrite H6.
      reflexivity.
      simpl in *.
      assert ((firstn (S n) b1) = 
        (firstn n b1 ++ (firstn 1 (skipn n b1)))).
      eapply firstn_S_app.
      rewrite H2.
      eapply Forall2_app.
      trivial.
      rewrite H6.
    
      Local Transparent firstn skipn.
      simpl.
      econstructor.
      trivial.
      econstructor.
    Qed.

    Theorem casKDF_support_eq :  forall ls1 k b a ls2 eqd1 eqd2 eqd3,
      In (a, b) (getSupport ((casKDF k ls1) _ eqd1 (rndHist eqd2 eqd3 rndRange) ls2)) ->
      skipn (length ls1) b = ls2 /\
      tl ((map (firstn digestLen) (snd (split (firstn (length ls1) b)))) ++ (k :: nil) ) = firstn (length ls1) (map (fun x => snd (snd x)) (fst (split b))).
  
      Local Opaque getSupport firstn skipn.

      induction ls1; intros; simpl in *.

      intuition.
      repeat simp_in_support.
      apply skipn_0.

      destruct a.
      simpl in *.
      repeat simp_in_support.
      destruct x.
      repeat simp_in_support.
      destruct x.
      repeat simp_in_support.
      eapply IHls1 in H1.
      intuition.
      subst.
      unfold rndHist in *.
      repeat simp_in_support.
      rewrite <- tl_skipn_eq.
      rewrite H4.
      reflexivity.

      destruct x.
      unfold rndHist in *.
      repeat simp_in_support.
      destruct x.
      repeat simp_in_support.
      eapply IHls1 in H1.
      intuition.

      symmetry.
      rewrite firstn_S_app.
      rewrite <- H2.
      symmetry.
      rewrite firstn_S_app.
      rewrite snd_split_app.
      rewrite map_app.
      rewrite tl_app_eq.
      f_equal.
      f_equal.
      f_equal.
      rewrite H.
      Local Transparent getSupport firstn skipn.
      simpl.
      trivial.

      rewrite map_split_l.
      rewrite skipn_map_eq.
      rewrite H.
      simpl.
      trivial.

      intuition.
      rewrite H in H1.
      simpl in *.
      eapply app_cons_not_nil; eauto.

    Qed.

    Theorem casKDF_rndHist_spec_NoDup : forall n ls1 k,
      length ls1 = n ->
      comp_spec (fun a b => NoDup (tl (b ++ k::nil)) -> NoDup (fst (split (snd a))))
      ((casKDF k ls1) _ _ (rndHist _ _ rndRange) nil)
      (rndList _ (rndOctetString digestLen) n).

      intuition.
      eapply comp_spec_consequence_support.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply list_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.

      eapply list_EqDec; eauto with typeclass_instances.
   
      eapply casKDF_rndHist_rndOctetString_spec.
      trivial.
      intuition.
      simpl in *.

      eapply casKDF_support_eq in H0.
      intuition.
      symmetry in H6.
      rewrite firstn_all2 in H6.
      eapply (@NoDup_map_inv _ _ (fun x : FullContext * (OctetString * OctetString) =>
        snd (snd x))).
      rewrite H6.
      eapply Forall2_map_eq in H5.
      rewrite map_split_r.
      rewrite H.
      rewrite H5.
      rewrite map_id.
      trivial.
      rewrite map_length.
      rewrite split_length_l.
      subst.
      eapply skipn_nil_impl_short; eauto.
    Qed.

    Theorem stripOpt_length : forall (A : Type)(ls : list (option A)) ls',
      stripOpt ls = Some ls' ->
      length ls' = length ls.

      induction ls; intuition; simpl in *.
      inversion H; clear H; subst.
      trivial.
      destruct a.
      simpl in *.
      case_eq (stripOpt ls); intros.
      rewrite H0 in H.
      simpl in *.
      inversion H; clear H; subst.
      simpl in *.
      rewrite IHls; eauto.
      rewrite H0 in H.  
      simpl in *.
      inversion H.
      simpl in *.
      inversion H.

    Qed.

    Theorem CasKDF_IND_CPA_G1_bad2_le : 
      Pr[CasKDF_IND_CPA_G1_bad1] <= Pr[CasKDF_IND_CPA_G1_bad2].

      unfold CasKDF_IND_CPA_G1_bad1, CasKDF_IND_CPA_G1_bad2.
      eapply comp_spec_impl_le.
      fcf_irr_l.
      eapply list_EqDec; eauto with typeclass_instances. 
      eapply compMap_wf.
      intuition.
      fcf_irr_l.
      eapply list_EqDec; eauto with typeclass_instances. 
      eapply compMap_wf.
      intuition.
      eapply responseFunc_wf.
      destruct a0; simpl in *.
      eapply in_combine_l; eauto.
      
      destOpt.
      fcf_skip.
      eapply casKDF_rndHist_spec_NoDup.
      apply compMap_length in H.
      apply compMap_length in H0.
      rewrite combine_length in H0.
      rewrite min_l in H0.
      rewrite combine_length.
      rewrite min_l.
      rewrite split_length_l.
      erewrite stripOpt_length; eauto.
      rewrite split_length_l.
      erewrite stripOpt_length; eauto.
      rewrite H0.
      rewrite combine_length.
      rewrite min_l.
      rewrite combine_length.
      rewrite min_l.
      rewrite split_length_r.
      rewrite H.
      trivial.
      repeat rewrite split_length_r.
      rewrite H.
      eapply (le_trans _ (length a0)).
      rewrite H0.
      reflexivity.
      eapply Nat.eq_le_incl.
      symmetry.
      erewrite stripOpt_length; eauto.

      rewrite combine_length.
      rewrite min_l.
      rewrite split_length_r.
      rewrite context_length.
      rewrite H.
      trivial.
      repeat rewrite split_length_r.
      rewrite H.
      eapply (le_trans _ (length a0)).
      rewrite H0.
      reflexivity.
      eapply Nat.eq_le_incl.
      symmetry.
      erewrite stripOpt_length; eauto.
      rewrite split_length_r.
      rewrite H.
      trivial.
  
      eapply comp_spec_ret; intuition.
      simpl in *.
      eapply not_NoDup_hasDup_true.
      intuition.
      eapply hasDup_true_not_NoDup in H5.
      intuition.
      trivial.

      fcf_irr_r.
      eapply rndList_wf.
      eapply rndOctetString_wf.
      eapply comp_spec_ret; intuition.
   
    Qed.

    Definition CasKDF_IND_CPA_G1_bad3 :=
      s2 <-$ rndList _ (rndOctetString digestLen) (pred (length KE));
      ret hasDup _ (s2 ++ psk :: nil).

    Theorem CasKDF_IND_CPA_G1_bad3_equiv : 
      Pr[CasKDF_IND_CPA_G1_bad2] == Pr[CasKDF_IND_CPA_G1_bad3].

      eapply comp_spec_eq_impl_eq.

      unfold CasKDF_IND_CPA_G1_bad2, CasKDF_IND_CPA_G1_bad3.
      fcf_skip.
      destruct (length KE).
      lia.
      eapply rndList_tl_eq.
      (* wf *)
      eapply compMap_wf; intuition.
      unfold rndOctet. wftac.
      simpl in *.
      subst.
      eapply comp_spec_ret; intuition.
      rewrite tl_app_eq.    
      reflexivity.
      eapply rndList_length in H.
      destruct a; simpl in *; intuition; discriminate.
    Qed.

    Definition CasKDF_IND_CPA_G1_bad4 :=
      s2 <-$ compMap _ (fun _ => rndOctetString digestLen) (forNats (pred (length KE)));
      ret hasDup _ (s2 ++ psk :: nil).

    Theorem CasKDF_IND_CPA_G1_bad4_equiv : 
      Pr[CasKDF_IND_CPA_G1_bad3] == Pr[CasKDF_IND_CPA_G1_bad4].

      eapply comp_spec_eq_impl_eq.

      unfold CasKDF_IND_CPA_G1_bad3, CasKDF_IND_CPA_G1_bad4.
      fcf_skip.
      eapply rndList_map_perm.
      eapply comp_spec_ret; intuition.
 
      match goal with
      | [|- context[hasDup ?eqd ?a] ] =>
        case_eq (hasDup eqd a); intros
      end.
      match goal with
      | [|- context[hasDup ?eqd ?a] ] =>
        case_eq (hasDup eqd a); intros
      end.
      trivial.
      eapply hasDup_true_not_NoDup in H2.
      intuition.
      eapply hasDup_false_NoDup in H3.
      eapply Permutation_NoDup.
      eapply Permutation_app.
      eapply Permutation_sym.
      eauto.
      eapply Permutation_refl.
      trivial.
      match goal with
      | [|- context[hasDup ?eqd ?a] ] =>
        case_eq (hasDup eqd a); intros
      end.
      eapply hasDup_true_not_NoDup in H3.
      intuition.
      eapply hasDup_false_NoDup in H2.
      eapply Permutation_NoDup.
      eapply Permutation_app.
      eauto.
      eapply Permutation_refl.
      trivial.
      trivial.

    Qed.

    Definition CasKDF_IND_CPA_G1_bad5 :=
      s2 <-$ compMap _ (fun _ => rndOctetString digestLen) (forNats (pred (length KE)));
      ret (if (in_dec (EqDec_dec _) psk s2) then true else false)
       || (hasDup _ s2).

    Theorem CasKDF_IND_CPA_G1_bad5_equiv :
      Pr[CasKDF_IND_CPA_G1_bad4] == Pr[CasKDF_IND_CPA_G1_bad5].

      unfold CasKDF_IND_CPA_G1_bad4, CasKDF_IND_CPA_G1_bad5.
      eapply comp_spec_eq_impl_eq.
      fcf_skip.
      eapply comp_spec_ret; intuition.
      
      match goal with
      | [|- context[if ?a then _ else _] ] =>
        destruct a
      end.
      simpl.
      eapply not_NoDup_hasDup_true.
      intuition.
      assert (NoDup ((psk :: nil) ++ b)).
      eapply Permutation_NoDup.
      eapply Permutation_app_comm.
      trivial.
      simpl in *.
      inversion H2; clear H2; subst.
      intuition.
      simpl.
      
      match goal with
      | [|- context[hasDup ?eqd ?a] ] =>
        case_eq (hasDup eqd a); intros
      end.
      match goal with
      | [|- context[hasDup ?eqd ?a] ] =>
        case_eq (hasDup eqd a); intros
      end.
      trivial.
      apply hasDup_false_NoDup in H2.
      apply hasDup_true_not_NoDup in H1.
      intuition.
      eapply app_NoDup.
      trivial.
      econstructor.
      simpl in *.
      intuition.
      econstructor.
      intuition.
      simpl in *.
      intuition.
      subst.
      intuition.
      intuition.
      simpl in *.
      intuition.
      subst.
      intuition.

      match goal with
      | [|- context[hasDup ?eqd ?a] ] =>
        case_eq (hasDup eqd a); intros
      end.
      apply hasDup_false_NoDup in H1.
      apply hasDup_true_not_NoDup in H2.
      intuition.
      eapply NoDup_app in H1.
      intuition.
      trivial.
      
    Qed.

    Definition CasKDF_IND_CPA_G1_bad5a :=
      s2 <-$ compMap _ (fun _ => rndOctetString digestLen) (forNats (pred (length KE)));
      ret (if (in_dec (EqDec_dec _) psk s2) then true else false).

    Definition CasKDF_IND_CPA_G1_bad5b :=
      s2 <-$ compMap _ (fun _ => rndOctetString digestLen) (forNats (pred (length KE)));
      ret (hasDup _ s2).
  
    Theorem CasKDF_IND_CPA_G1_bad5_split : 
      Pr[CasKDF_IND_CPA_G1_bad5] <= Pr[CasKDF_IND_CPA_G1_bad5a] + Pr[CasKDF_IND_CPA_G1_bad5b].

      apply evalDist_orb_le.
    Qed.

    Theorem rndOctetString_uniform : forall n ls,
      length ls = n ->
      evalDist (rndOctetString n) ls == expRat (1 / 2) (8 * n).

      unfold rndOctetString in *.
      induction n; intuition.
      simpl in *.
      match goal with
      | [|- context[ if ?a then _ else _] ] =>
        destruct a
      end.
      reflexivity.
      destruct ls; simpl in *; intuition; discriminate.

      unfold forNats.
      fold forNats.
      unfold compMap.
      fold compMap.
      destruct ls.
      simpl in *. discriminate.
      simpl in H.
      eapply eqRat_trans.
      eapply (@evalDist_seq_case_split_eq _ (eqb b)).
      unfold rndOctet. wftac.
      rewrite <- evalDist_event_equiv.
      eapply uniformity.
      intros.
      eapply (@evalDist_seq_case_split_eq _ (eqb ls)).
      eapply compMap_wf.
      intros.
      unfold rndOctet. wftac.
      rewrite <- evalDist_event_equiv.
      eauto.
      intros.
      simpl.
      match goal with
      | [|- context[ if ?a then _ else _] ] =>
        destruct a
      end.
      reflexivity.
      rewrite eqb_leibniz in H0.
      rewrite eqb_leibniz in H1.
      subst.
      intuition.
      intros.
      simpl.
      match goal with
      | [|- context[ if ?a then _ else _] ] =>
        destruct a
      end.
      inversion e; clear e; subst.
      rewrite eqb_refl in *.
      discriminate.
      reflexivity.
      intros.
      fcf_irr_l.
      eapply compMap_wf.
      intros.
      unfold rndOctet. wftac.
      simpl.
      match goal with
      | [|- context[ if ?a then _ else _] ] =>
        destruct a
      end.
      inversion e; clear e; subst.
      rewrite eqb_refl in *.
      discriminate.
      reflexivity.
      repeat rewrite ratMult_0_r.
      repeat rewrite <- ratAdd_0_r.
      rewrite ratMult_1_r.
      
      cutrewrite (8 * (S n) = 8 + (8 * n))%nat.
      rewrite expRat_exp_sum.
      eapply ratMult_eqRat_compat.
      rewrite expRat_terms.
      simpl.
      reflexivity.
      reflexivity.
      lia.

      Unshelve.
      apply (oneVector 8).
    Qed.

    Theorem rndOctetString_0 : forall n ls,
      length ls <> n ->
      evalDist (rndOctetString n) ls == 0.

      induction n; intuition.
      simpl.
      match goal with
      | [|- context[ if ?a then _ else _] ] =>
        destruct a
      end.
      subst.
      simpl in *. intuition.
      reflexivity.

      unfold rndOctetString.
      unfold forNats.
      fold forNats.
      unfold compMap.
      fold compMap.
      destruct ls.

      fcf_irr_l.
      unfold rndOctet; wftac.
      fcf_irr_l.
      eapply compMap_wf; intros.
      unfold rndOctet; wftac.
      simpl.
      match goal with
      | [|- context[ if ?a then _ else _] ] =>
        destruct a
      end.
      discriminate.
      reflexivity.

      eapply eqRat_trans.
      eapply (@evalDist_seq_case_split_eq _ (eqb b)).
      unfold rndOctet.
      wftac.
      rewrite <- evalDist_event_equiv.
      reflexivity.
      intuition.
  
      eapply (@evalDist_seq_case_split_eq _ (eqb ls)).
      eapply compMap_wf; intros.
      unfold rndOctet; wftac.
      rewrite <- evalDist_event_equiv.
      eapply IHn.
      intuition.
      simpl in *. lia.
      intuition.
      simpl.
      match goal with
      | [|- context[ if ?a then _ else _] ] =>
        destruct a
      end.
      reflexivity.
      rewrite eqb_leibniz in H0.
      rewrite eqb_leibniz in H1.
      subst.
      intuition.
      intros.
      simpl.
      match goal with
      | [|- context[ if ?a then _ else _] ] =>
        destruct a
      end.
      inversion e; clear e; subst.
      rewrite eqb_refl in *.
      discriminate.
      reflexivity.
      intuition.
      fcf_irr_l.
      eapply compMap_wf; intros.
      unfold rndOctet; wftac.
      simpl.
      match goal with
      | [|- context[ if ?a then _ else _] ] =>
        destruct a
      end.
      inversion e; clear e; subst.
      rewrite eqb_refl in *.
      discriminate.
      reflexivity.
      repeat rewrite ratMult_0_r.
      repeat rewrite ratMult_0_l.
      repeat rewrite <- ratAdd_0_r.
      apply ratMult_0_r.

    Qed.

    Theorem rndOctetString_uniform_le : forall n ls,
      evalDist (rndOctetString n) ls <= expRat (1 / 2) (8 * n).

      intuition.
      destruct (eq_nat_dec (length ls) n).
      rewrite rndOctetString_uniform.
      reflexivity.
      trivial.

      rewrite rndOctetString_0.
      eapply rat0_le_all.
      trivial.
    Qed.

    Theorem CasKDF_IND_CPA_G1_bad5a_small :
      Pr[CasKDF_IND_CPA_G1_bad5a] <= (pred (length KE)) / 1 * expRat (1 / 2) (8 * digestLen).

      unfold CasKDF_IND_CPA_G1_bad5a.
      eapply leRat_trans.
      eapply RndListIn_Prob.
      rewrite rndOctetString_uniform_le.
      rewrite forNats_length.
      reflexivity.

    Qed.

    Theorem CasKDF_IND_CPA_G1_bad5b_small :
      Pr[CasKDF_IND_CPA_G1_bad5b] <= (pred (length KE)) * (pred (length KE)) / 1 * expRat (1 / 2) (8 * digestLen).
  
      unfold CasKDF_IND_CPA_G1_bad5b.
      specialize (@DupList_Prob _ _ (rndOctetString digestLen) (rndOctetString_wf digestLen) (expRat (1 / 2) (8 * digestLen)) (rndOctetString_uniform_le digestLen)
        _ (forNats (Init.Nat.pred (length KE)))); intros.
      rewrite H.
      rewrite forNats_length.
      reflexivity.
    Qed.

    Theorem CasKDF_IND_CPA_G1_bad5_small : 
      Pr[CasKDF_IND_CPA_G1_bad5] <= (length KE) * (length KE) / 1 * expRat (1 / 2) (8 * digestLen).

      rewrite CasKDF_IND_CPA_G1_bad5_split.
      rewrite CasKDF_IND_CPA_G1_bad5a_small.
      rewrite CasKDF_IND_CPA_G1_bad5b_small.
      destruct (length KE).
      lia.
      unfold pred.
      eapply leRat_trans.
      2:{
      eapply ratMult_leRat_compat.
      eapply leRat_terms.
      eapply mult_le_compat.
      reflexivity.
      eapply PeanoNat.Nat.le_succ_diag_r.
      reflexivity.
      reflexivity.
      }
      eapply leRat_trans.
      2:{
      eapply eqRat_impl_leRat.
      symmetry.
      rewrite Nat.mul_succ_l.
      rewrite ratAdd_den_same.
      eapply ratMult_distrib_r.
      }
      rewrite ratAdd_comm.
      reflexivity.
    Qed.

    Theorem CasKDF_IND_CPA_G1c_G2_equiv : 
      Pr[x <-$ CasKDF_IND_CPA_G1c; ret (fst x)] == Pr[CasKDF_IND_CPA_G2].

      unfold CasKDF_IND_CPA_G1c, CasKDF_IND_CPA_G2.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      destOpt.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      reflexivity.

      fcf_simp.
      reflexivity.

    Qed.
  
    Theorem eqRat_terms_proj : forall n1 d1 n2 d2,
      n1 = n2 ->
      proj1_sig d1 = proj1_sig d2 ->
      RatIntro n1 d1 == RatIntro n2 d2.

      intuition.
      unfold proj1_sig in *.
      destruct d1.
      destruct d2.
      subst.
      rattac.
    Qed.

    Theorem CasKDF_IND_CPA_G1_G2_close : 
      | Pr[CasKDF_IND_CPA_G1] - Pr[CasKDF_IND_CPA_G2] | <= (length KE) * (length KE) / 2 ^ (8 * digestLen).

      rewrite CasKDF_IND_CPA_G1a_equiv.
      rewrite CasKDF_IND_CPA_G1b_equiv. 
      rewrite <- CasKDF_IND_CPA_G1c_G2_equiv.
      rewrite CasKDF_IND_CPA_G1bc_close.
      rewrite CasKDF_IND_CPA_G1bc_bad_eq.
      rewrite CasKDF_IND_CPA_G1_bad1_equiv.
      rewrite CasKDF_IND_CPA_G1_bad2_le.
      rewrite CasKDF_IND_CPA_G1_bad3_equiv.
      rewrite CasKDF_IND_CPA_G1_bad4_equiv.
      rewrite CasKDF_IND_CPA_G1_bad5_equiv.
      rewrite CasKDF_IND_CPA_G1_bad5_small.
      eapply eqRat_impl_leRat.
      rewrite expRat_terms.
      rewrite <- ratMult_num_den.
      eapply eqRat_terms.
      rewrite expnat_1.
      rewrite mult_1_r.
      trivial.
      rewrite posnatMult_eq.
      rewrite mult_1_l.
      unfold posnatToNat, natToPosnat.
      reflexivity.
      
      Unshelve.
      eapply expnat_nz.
      intuition.
    Qed.

    (* split/reorder *)
    Definition CasKDF_IND_CPA_G3 :=
      SK_strong <-$ @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      R_strong <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) (snd SK_strong) );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1 <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2 <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match (stripOpt (lsR1 ++ R_strong::lsR2)) with
      | None => ret false
      | Some lsR =>
        [sk, Ps] <-2 (fst (split (lsSK1 ++ (SK_strong :: lsSK2))), snd (split (lsSK1 ++ (SK_strong :: lsSK2))));
        [ks, Rs] <-2 (fst (split lsR), snd (split lsR));
        [k, st] <-$2 (casKDF psk (combine ks (combine (combine Ps Rs) context)))  _ _ (rndHist _ _ rndRange) nil;
        [b, _] <-$2 (B Ps (first k, Rs) (last k nil)) _ _ (randomFunc rndRange _) st;
        ret b
      end.

    Theorem CasKDF_IND_CPA_G3_equiv : 
      Pr[CasKDF_IND_CPA_G2] == Pr[CasKDF_IND_CPA_G3].

      apply CtKDF_SplitReorder_equiv; intuition.
    Qed.

   (* split calls to casKDF *)
    Definition CasKDF_IND_CPA_G4 :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      R_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match R_opt with
      | None => ret false
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret false
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret false
          | Some lsR2 =>
            [cs1, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            [x2, st2] <-$2 (rndHist _ _ rndRange st1
                  ((P, R, (nth strongKE context nil)), (k_strong, cs1)));
            cs2 <- firstn digestLen x2;
            k2 <- skipn digestLen x2;
            [k, st3] <-$2 (casKDF cs2
              (combine 
                (fst (split lsR2)) 
                (combine 
                  (combine (snd (split lsSK2)) (snd (split lsR2)))
                  (skipn (S strongKE) context)
                )
              )) _ _ (rndHist _ _ rndRange) st2;

            [b, _] <-$2 (
              (B (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) (last (k2 ::k) nil))
            ) _ _ (randomFunc rndRange _) st3;
            ret b
          end
        end
      end.

    Definition CasKDF_IND_CPA_G3a :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      R <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1 <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2 <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match (stripOpt (lsR1 ++ R :: lsR2)) with
      | None => ret false
      | Some lsR =>
        [k, st] <-$2 
          (casKDF psk (combine (fst (split lsR)) (combine (combine (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (snd (split lsR))) context)))
          _ _ (rndHist _ _ rndRange) nil;
        [b, _] <-$2 (
          (B (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first k, (snd (split lsR))) (last k nil))
        ) _ _ (randomFunc rndRange _) st;
        ret b
      end.

    Theorem CasKDF_IND_CPA_G3a_equiv :
      Pr[CasKDF_IND_CPA_G3] == Pr[CasKDF_IND_CPA_G3a].

      Local Opaque evalDist.

      unfold CasKDF_IND_CPA_G3, CasKDF_IND_CPA_G3a.
      fcf_skip.
      fcf_simp.
      fcf_skip. 
      reflexivity.
      fcf_simp.
      fcf_skip.
      fcf_skip.
      fcf_skip.
      fcf_skip.
      simpl.
      destOpt.
      fcf_inline_first.
      fcf_skip.
      repeat rewrite fst_split_app.
      repeat rewrite fst_split_cons.
      repeat rewrite snd_split_app.
      repeat rewrite snd_split_cons.
      reflexivity.
      fcf_inline_first.
      fcf_simp.
      fcf_inline_first.
      fcf_simp.
      fcf_skip.
      repeat rewrite fst_split_app.
      repeat rewrite fst_split_cons.
      repeat rewrite snd_split_app.
      repeat rewrite snd_split_cons.
      reflexivity.
      reflexivity.
    Qed.

    Theorem last_app_eq : forall (A : Type)(ls1 ls2 : list A)(def : A),
      ls2 <> nil ->
      last (ls1 ++ ls2) def = last ls2 def.

      induction ls1; intuition; simpl in *.
      rewrite IHls1.
      destruct ls1; simpl in *.
      destruct ls2; simpl in *; intuition idtac.
      trivial.
      trivial.

    Qed.

    Theorem casKDF_keys_length : forall ps cs ls (S : Set)(eqds : EqDec S) x o (s : S),
      In (ls, x) (getSupport ((casKDF cs ps) _ _ o s)) ->
      length ls = length ps.

      induction ps; intuition idtac.
      simpl in *.
      intuition. pairInv.
      trivial.

      unfold casKDF in *.
      fold casKDF in *.
      unfold evalDist_OC in *.
      fold evalDist_OC in *.
      repeat simp_in_support.
      destruct x0.
      repeat simp_in_support.
      destruct x0.
      repeat simp_in_support.
      eapply IHps in H1.
      simpl.
      lia.

    Qed.

    Theorem CasKDF_IND_CPA_G3a_G4_equiv : 
      Pr[CasKDF_IND_CPA_G3a] == Pr[CasKDF_IND_CPA_G4].

      Local Opaque evalDist.

      unfold CasKDF_IND_CPA_G3a, CasKDF_IND_CPA_G4.
      fcf_skip.
      fcf_simp.
      fcf_skip.
      fcf_simp.
      do 4 fcf_skip.
      destruct x.
      destruct p.
      rewrite stripOpt_app.
      case_eq (stripOpt x2); intros.
      simpl.
      case_eq (stripOpt x3); intros.
      simpl.
      rewrite (@lsAppCons _ context strongKE nil).
      repeat rewrite fst_split_app.
      repeat rewrite snd_split_app.
      simpl.
      remember (split l0) as z. destruct z.
      simpl.
      repeat rewrite combine_app.
      repeat rewrite combine_cons.
      eapply eqRat_trans.
      eapply evalDist_seq_eq_trans.
      intros.
      eapply casKDF_app.
      unfold evalDist_OC.
      fold evalDist_OC.
      fcf_inline_first.
      fcf_skip.
      rewrite firstn_app.
      rewrite firstn_length.
      rewrite min_l.
      rewrite minus_diag.
      simpl.
      rewrite app_nil_r.
      rewrite firstn_firstn.
      reflexivity.
      trivial.
      lia.
     
      fcf_inline_first.
      fcf_simp.
      eapply eqRat_trans.
      eapply evalDist_seq_eq_trans.
      intros. 
      unfold evalDist_OC.
      fold evalDist_OC.
      eapply evalDist_seq_eq_trans.
      intros.
      eapply casKDF_cons.
      unfold evalDist_OC.
      fold evalDist_OC.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      fcf_inline_first.
      fcf_skip.
      rewrite (app_cons_eq (firstn strongKE context)).
      cutrewrite ((S strongKE) = length ((firstn strongKE context ++
                  nth strongKE context nil
                  :: nil))).
      simpl.
      eapply evalDist_comp_equal.
      f_equal.
      f_equal.
      f_equal.
      f_equal.
      f_equal.
      rewrite (@lsAppCons _ context strongKE nil) at 1.
      f_equal.
      rewrite <- app_assoc.
      f_equal. 
      cutrewrite <- ((S strongKE) = length ((firstn strongKE context ++
                  nth strongKE context nil
                  :: nil))).
      reflexivity.
    
      rewrite app_length.
      simpl. 
      rewrite firstn_length.
      rewrite min_l.
      lia.
      lia.
      lia.
      f_equal.
      f_equal.
      f_equal.
      f_equal.
      f_equal.
      erewrite (@lsAppCons _ _ strongKE nil) at 1.
      simpl.
      rewrite <- app_assoc.
      reflexivity.
      eapply lt_le_trans.
      eapply strongKE_small.
      rewrite <- context_length.
      reflexivity.

      rewrite app_length.
      simpl. 
      rewrite firstn_length.
      rewrite min_l.
      lia.
      lia.

      fcf_simp.
      fcf_inline_first.
      fcf_skip.
      rewrite last_app_eq.
      reflexivity.
      intuition idtac.
      discriminate.
      
      rewrite combine_length.
      apply compMap_length in H1.
      rewrite firstn_length in H1.
      rewrite min_l in H1.
      apply compMap_length in H3.
      rewrite combine_length in H3.
      rewrite min_l in H3.
      rewrite firstn_length in H3.
      rewrite min_l in H3.
      rewrite min_r.
      rewrite split_length_l.
      rewrite firstn_length.
      rewrite min_l.
      erewrite stripOpt_length; eauto. 
      lia.
      rewrite combine_length.
      repeat rewrite split_length_r.
      rewrite min_l.
      rewrite firstn_length.
      rewrite min_l.
      lia.
      lia.
      erewrite (@stripOpt_length _ _ l); eauto.
      lia.
      lia.
      rewrite firstn_length.
      rewrite min_l.
      rewrite split_length_r.
      lia.
      lia.
      lia.

      rewrite combine_length.
      apply compMap_length in H1.
      rewrite firstn_length in H1.
      rewrite min_l in H1.
      apply compMap_length in H3.
      rewrite combine_length in H3.
      rewrite min_l in H3.
      rewrite firstn_length in H3.
      rewrite min_l in H3.
      rewrite min_r.
      rewrite split_length_r.
      rewrite firstn_length.
      rewrite min_l.
      erewrite stripOpt_length; eauto.
      trivial.  
      lia.
      repeat rewrite split_length_r.
      erewrite stripOpt_length; eauto.
      lia.
      lia.
      rewrite firstn_length.
      rewrite min_l.
      rewrite split_length_r.
      lia.
      lia.
      lia.
    
      apply compMap_length in H1.
      rewrite firstn_length in H1.
      rewrite min_l in H1.
      apply compMap_length in H3.
      rewrite combine_length in H3.
      rewrite min_l in H3.
      rewrite firstn_length in H3.
      rewrite min_l in H3.
      repeat rewrite split_length_r.
      erewrite (@stripOpt_length _ _ l); eauto. 
      lia.
      lia.
      rewrite firstn_length.
      rewrite min_l.
      rewrite split_length_r.
      lia.
      lia.
      lia.
      lia.

      simpl.
      reflexivity.

      simpl.
      reflexivity.
    
      rewrite stripOpt_app.
      destruct (stripOpt x2).
      simpl.
      reflexivity.
      simpl.
      reflexivity.

      Local Transparent evalDist.

    Qed.

    Theorem CasKDF_IND_CPA_G4_equiv : 
      Pr[CasKDF_IND_CPA_G3] == Pr[CasKDF_IND_CPA_G4].

      rewrite CasKDF_IND_CPA_G3a_equiv.
      apply CasKDF_IND_CPA_G3a_G4_equiv.
    Qed.

    (* make the parts of the cascade independent *)
    Definition CasKDF_IND_CPA_G5 :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret false
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret false
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret false
          | Some lsR2 =>
            [cs1, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            cs2 <-$ rndOctetString digestLen;
            k2 <-$ rndOctetString secretLen;
            st2 <- (((P, R, (nth strongKE context nil)), (k_strong, cs1)), (cs2 ++ k2));
            [k, st3] <-$2 (casKDF cs2
              (combine 
                (fst (split lsR2)) 
                (combine 
                  (combine (snd (split lsSK2)) (snd (split lsR2)))
                  (skipn (S strongKE) context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;

            [b, _] <-$2 (
              (B (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) (last (k2::k) nil))
            ) _ _ (randomFunc rndRange _) (st3 ++ st2 :: st1);
            ret b
          end
        end
      end.

    Definition CasKDF_IND_CPA_G4a :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret false
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret false
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret false
          | Some lsR2 =>

            [cs1, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            [x2, st2] <-$2 
              (k2 <-$ (ka <-$ rndOctetString digestLen; kb <-$ rndOctetString secretLen; ret (ka ++ kb));
              ret (k2, (((P, R, (nth strongKE context nil)), (k_strong, cs1)), k2))
              );
            cs2 <- firstn digestLen x2;
            k2 <- skipn digestLen x2;
            [k, st3] <-$2 (casKDF cs2
              (combine 
                (fst (split lsR2)) 
                (combine 
                  (combine (snd (split lsSK2)) (snd (split lsR2)))
                  (skipn (S strongKE) context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;

            [b, _] <-$2 (
              (B (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k),(snd (split lsR1) ++ (R :: (snd (split lsR2))))) (last (k2::k) nil))
            ) _ _ (randomFunc rndRange _) (st3 ++ st2 :: st1);
            ret b
          end
        end
      end.

    Theorem rndOctetString_app_eq : forall n1 n2 x,
      evalDist (rndOctetString (n1 + n2)) x ==
      evalDist (a <-$ rndOctetString n1; b <-$ rndOctetString n2; ret (a ++ b)) x.

      intros.
      unfold rndOctetString.
      rewrite <- compMap_app.
      eapply compMap_eq.
      eapply forNats_list_pred_app.
      intuition idtac.
      reflexivity.

    Qed.

    Theorem CasKDF_IND_CPA_G4a_equiv : 
      Pr[CasKDF_IND_CPA_G4] == Pr[CasKDF_IND_CPA_G4a].

      unfold CasKDF_IND_CPA_G4, CasKDF_IND_CPA_G4a.
      eapply comp_spec_eq_impl_eq.
      fcf_skip.
      fcf_skip.
      fcf_skip.
      fcf_skip.
      fcf_skip.
      fcf_skip.
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      fcf_skip.
      fcf_skip.
      unfold rndHist.
      fcf_skip.
      unfold rndRange.
      eapply eq_impl_comp_spec_eq.
      intros.
      eapply rndOctetString_app_eq.
      subst.  
      eapply (@comp_spec_ret _ _ _ _ _ _ (fun a b => fst a = fst b /\ snd a = (snd b)::b5)).
      intuition.
      simpl in *.
      intuition. subst.   
      fcf_simp.
      simpl.
      fcf_skip.
      eapply (fcf_oracle_eq (fun a b => a = b++(p :: b5))).
      reflexivity.
      intuition.
      subst.
      unfold rndHist.
      fcf_skip.
      eapply comp_spec_ret; intuition.
      simpl in *; intuition; subst.
      fcf_simp.
      fcf_skip.

      eapply comp_spec_eq_refl.
      eapply comp_spec_eq_refl.
      eapply comp_spec_eq_refl.
    
    Qed.

    Theorem CasKDF_IND_CPA_G4a_G5_equiv : 
      Pr[CasKDF_IND_CPA_G4a] == Pr[CasKDF_IND_CPA_G5].

      unfold CasKDF_IND_CPA_G4a, CasKDF_IND_CPA_G5.
      do 6 (fcf_skip; fcf_simp).
      destOpt.
      fcf_simp.
      destOpt.
      destOpt.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      fcf_skip.
      
      apply compMap_length in H5.
      rewrite forNats_length in H5.
      rewrite <- H5.
      rewrite firstn_app_eq.
      reflexivity.
      fcf_simp.
      apply compMap_length in H5.
      rewrite forNats_length in H5.
      rewrite <- H5.
      rewrite skipn_app.
      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.
    Qed.

    Theorem CasKDF_IND_CPA_G5_equiv : 
      Pr[CasKDF_IND_CPA_G4] == Pr[CasKDF_IND_CPA_G5].

      rewrite CasKDF_IND_CPA_G4a_equiv.
      eapply CasKDF_IND_CPA_G4a_G5_equiv.

    Qed.

    Theorem CasKDF_G1_G5_close : 
      | Pr[CasKDF_IND_CPA_G1] - Pr[CasKDF_IND_CPA_G5] | <= (length KE) * (length KE) / 2 ^ (8 * digestLen).

      rewrite <- CasKDF_IND_CPA_G5_equiv.
      rewrite <- CasKDF_IND_CPA_G4_equiv.
      rewrite <- CasKDF_IND_CPA_G3_equiv.
      eapply CasKDF_IND_CPA_G1_G2_close.
      
    Qed.

    End CasKDF_SplitReorder.

    Theorem CasKDF_IND_CPA_G1_equiv : 
      Pr [ExpROM _ _ rndRange _ (KeyExchangeCPA_ROM_G0 A) ] == Pr[CasKDF_IND_CPA_G1 A].

      Local Opaque evalDist.

      unfold ExpROM, KeyExchangeCPA_ROM_G0, CasKDF_IND_CPA_G1.
      simpl.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_simp.
      fcf_skip.
      destOpt.
      fcf_inline_first.
      fcf_skip.
      reflexivity.
      fcf_inline_first.
      fcf_simp.
      fcf_inline_first.
      fcf_skip.
      reflexivity.

      simpl.
      fcf_inline_first.
      reflexivity.

      Local Transparent evalDist.

    Qed.

    (* give random value to adversary *)
    Definition CasKDF_IND_CPA_G6 :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret false
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret false
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret false
          | Some lsR2 =>
            [cs1, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            cs2 <-$ rndOctetString digestLen;
            k2 <-$ rndOctetString secretLen;
            st2 <- (((P, R, (nth strongKE context nil)), (k_strong, cs1)), (cs2 ++ k2));
            [k3, st3] <-$2 (casKDF cs2
              (combine 
                (fst (split lsR2)) 
                (combine 
                  (combine (snd (split lsSK2)) (snd (split lsR2)))
                  (skipn (S strongKE) context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            k <-$ rndOctetString secretLen;
            [b, _] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k3), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
            ) _ _ (randomFunc rndRange _) (st3 ++ st2 :: st1);
            ret b
          end
        end
      end.

    (* use nested oracle to expose bad event *)
    Definition CasKDF_IND_CPA_G5a :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret (false, false)
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret (false, false)
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret (false, false)
          | Some lsR2 =>
            [cs1, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            cs2 <-$ rndOctetString digestLen;
            k2 <-$ rndOctetString secretLen;
            [k, st3] <-$2 (casKDF cs2
              (combine 
                (fst (split lsR2)) 
                (combine 
                  (combine (snd (split lsSK2)) (snd (split lsR2)))
                  (skipn (S strongKE) context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            st2 <- (((P, R, (nth strongKE context nil)), (k_strong, cs1)), (cs2 ++ k2));
            [b, s] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) (last (k2::k) nil))
            ) _ _ (nestedRandomFunc _ _ rndRange (st3 ++ st2::st1)) nil;
            ret (b, any_dec (fun x => if (arrayLookup _ (st3 ++ st2 :: nil) x) then true else false) (fst (split s)))
          end
        end
      end.

    Theorem CasKDF_IND_CPA_G5a_equiv : 
      Pr[CasKDF_IND_CPA_G5 A] == Pr[x <-$ CasKDF_IND_CPA_G5a; ret (fst x)].

      unfold CasKDF_IND_CPA_G5, CasKDF_IND_CPA_G5a.
      eapply comp_spec_eq_impl_eq.
      do 6 (
      fcf_inline_first;
      fcf_skip;
      fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
  
      do 5 (
      fcf_inline_first;
      fcf_skip;
      fcf_simp).

      eapply (fcf_oracle_eq (nestedRandomFunc_pred _ 
        (b8 ++
   (b, o0, nth strongKE context nil,
   (o, a), b0++b7)::b5))).
      unfold nestedRandomFunc_pred.
      intuition.
      rewrite app_nil_r.
      reflexivity.
      intuition.
      eapply nestedRandomFunc_spec.
      trivial.
      simpl in *.
      intuition. subst.
      eapply comp_spec_eq_refl.

      fcf_simp.
      eapply comp_spec_eq_refl.
      fcf_simp.
      eapply comp_spec_eq_refl.
      fcf_simp.
      eapply comp_spec_eq_refl.

    Qed.

    (* don't put any of the "bad" information in the oracle. equal up to bad to the last game *)
    Definition CasKDF_IND_CPA_G5b :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret (false, false)
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret (false, false)
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret (false, false)
          | Some lsR2 =>
            [cs1, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            
            [kls, k, st3] <-$3 (
              cs2 <-$ rndOctetString digestLen;
              k2 <-$ rndOctetString secretLen;
              [k, st3] <-$2 (casKDF cs2
                (combine 
                  (fst (split lsR2)) 
                  (combine 
                    (combine (snd (split lsSK2)) (snd (split lsR2)))
                    (skipn (S strongKE) context)
                  )
                )) _ _ (rndHist _ _ rndRange) nil;
              ret (first (k2 :: k), last (k2 :: k) nil, st3)
            );
            st2 <- (((P, R, (nth strongKE context nil)), (k_strong, cs1)), (@nil Octet));
            [b, s] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) ((k1++kls), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
            ) _ _ (nestedRandomFunc _ _ rndRange st1) nil;
            ret (b, any_dec (fun x => if (arrayLookup _ (st3 ++ st2 :: nil) x) then true else false) (fst (split s)))
          end
        end
      end.

    Theorem first_app_eq : forall (A : Type)(ls1 ls2 : list A),
      ls2 <> nil ->
      first (ls1 ++ ls2) = ls1 ++ (first ls2).

      unfold first in *; intros.
      destruct ls2; simpl in *. 
      intuition idtac.
      rewrite app_length.
      simpl.
      rewrite plus_comm.
      simpl.
      rewrite plus_comm.
      apply firstn_app_2.

    Qed.

    Theorem CasKDF_IND_CPA_G5ab_eq_until_bad : forall x,
      evalDist CasKDF_IND_CPA_G5a (x, false) == evalDist CasKDF_IND_CPA_G5b (x, false).

      unfold CasKDF_IND_CPA_G5a, CasKDF_IND_CPA_G5b.
      intros.
      eapply comp_spec_impl_eq.
      do 6 (fcf_skip; fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      fcf_skip.
      fcf_simp.
      do 3 (fcf_inline_first; fcf_skip; fcf_simp).
      fcf_skip.
      rewrite first_app_eq.
      eapply (fcf_oracle_eq_until_bad 
        (any_dec (fun y => if (arrayLookup _ 
          (b8 ++
         (b, o0, nth strongKE context nil,
         (o, a), b0++b7) :: nil) (fst y)) then true else false))
        (any_dec (fun y => if (arrayLookup _ 
          (b8 ++
         (b, o0, nth strongKE context nil,
         (o, a), b0++b7) :: nil) (fst y)) then true else false))
        (fun x y => forall z, arrayLookup _ x z = arrayLookup _ y z)
      ).
      trivial.
      intros.
      eapply nestedRandomFunc_wf.
      eapply rndOctetString_wf.
      intros.
      eapply nestedRandomFunc_wf.
      eapply rndOctetString_wf.
      intros.

      rewrite (app_cons_eq _ b5).
      eapply comp_spec_consequence.
      eapply nestedRandomFunc_app_spec.
      wftac.

      intuition.
      intuition.
      intuition.

      unfold nestedRandomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H23 in H22.
      simp_in_support.
      rewrite any_dec_cons.
      rewrite H21.
      apply orb_true_r.
      rewrite H23 in H22.
      unfold randomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H24 in H22.
      simp_in_support.    
      trivial.
      rewrite H24 in H22.
      repeat simp_in_support.
      rewrite any_dec_cons.
      rewrite H21.
      apply orb_true_r.
      
      intuition.
      unfold nestedRandomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H23 in H22.
      simp_in_support.
      rewrite any_dec_cons.
      rewrite H21.
      apply orb_true_r.
      rewrite H23 in H22.
      unfold randomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H24 in H22.
      simp_in_support.    
      trivial.
      rewrite H24 in H22.
      repeat simp_in_support.
      rewrite any_dec_cons.
      rewrite H21.
      apply orb_true_r.

      intros.
      trivial.

      trivial.
      intuition idtac.
      discriminate.

      fcf_simp.
      eapply comp_spec_ret; intuition.
      pairInv.
      simpl in *.
      rewrite fst_split_map_eq in H28.
      rewrite <- any_dec_map in H28.
      intuition.
      subst.
      f_equal.
      rewrite fst_split_map_eq.
      rewrite <- any_dec_map.
      rewrite H28.
      rewrite fst_split_map_eq.
      rewrite <- any_dec_map.
      symmetry.
      rewrite <- H28 at 1.
      rewrite H24.
      eapply any_dec_f_eq.
      intros.
      match goal with
      | [|- context[arrayLookup ?eqd (?a ++ ?b) ?c] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      erewrite arrayLookup_app_Some; eauto.
      repeat rewrite arrayLookup_app_None.
      simpl.
      match goal with
      | [|- context[if (if ?a then _ else _) then _ else _] ] =>
        case_eq a; intros
      end.
      trivial. 
      trivial.
      trivial.
      trivial.

      pairInv.
      simpl in *.
      rewrite fst_split_map_eq in H28.
      rewrite <- any_dec_map in H28.
      match goal with
      | [H: ?a -> _ |- _] =>
        cut a
      end; intuition.
      subst.
      f_equal.
      rewrite fst_split_map_eq.
      rewrite <- any_dec_map.
      rewrite H28.
      
      rewrite fst_split_map_eq.
      rewrite <- any_dec_map.
      symmetry.
      rewrite <- H28 at 1.
      rewrite H24.
      eapply any_dec_f_eq.
      intros.
      match goal with
      | [|- context[arrayLookup ?eqd (?a ++ ?b) ?c] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      erewrite arrayLookup_app_Some; eauto.
      repeat rewrite arrayLookup_app_None.
      simpl.
      match goal with
      | [|- context[if (if ?a then _ else _) then _ else _] ] =>
        case_eq a; intros
      end.
      trivial. 
      trivial.
      trivial.
      trivial.

      rewrite H24.
      symmetry.
      rewrite <- H28 at 1.
      eapply any_dec_f_eq.
      intros.
      match goal with
      | [|- context[arrayLookup ?eqd (?a ++ ?b) ?c] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      erewrite arrayLookup_app_Some; eauto.
      repeat rewrite arrayLookup_app_None.
      simpl.
      match goal with
      | [|- context[if (if ?a then _ else _) then _ else _] ] =>
        case_eq a; intros
      end.
      trivial. 
      trivial.
      trivial.
      trivial.

      fcf_simp.
      eapply comp_spec_ret; intuition.
      fcf_simp.
      eapply comp_spec_ret; intuition.
      eapply comp_spec_ret; intuition.

    Qed.


    Theorem CasKDF_IND_CPA_G5ab_bad_same : 
      Pr[x <-$ CasKDF_IND_CPA_G5a; ret (snd x)] == Pr[x <-$ CasKDF_IND_CPA_G5b; ret (snd x)].

      unfold CasKDF_IND_CPA_G5a, CasKDF_IND_CPA_G5b.
      intros.
      eapply comp_spec_impl_eq.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      do 4 (fcf_inline_first; fcf_skip; fcf_simp).
      fcf_inline_first; fcf_skip.

      rewrite first_app_eq.
      eapply (fcf_oracle_eq_until_bad 
        (any_dec (fun y => if (arrayLookup _ 
          (b8 ++
         (b, o0, nth strongKE context nil,
         (o, a), b0++b7) :: nil) (fst y)) then true else false))
        (any_dec (fun y => if (arrayLookup _ 
          (b8 ++
         (b, o0, nth strongKE context nil,
         (o, a), b0++b7) :: nil) (fst y)) then true else false))
        (fun x y => forall z, arrayLookup _ x z = arrayLookup _ y z)
      ).
      trivial.
      intros.
      eapply nestedRandomFunc_wf.
      eapply rndOctetString_wf.
      intros.
      eapply nestedRandomFunc_wf.
      eapply rndOctetString_wf.
      intros.

      rewrite (app_cons_eq _ b5).
      eapply comp_spec_consequence.
      eapply nestedRandomFunc_app_spec.
      eauto.

      intuition.
      intuition.
      intuition.
      intuition.

      unfold nestedRandomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H23 in H22.
      simp_in_support.
      rewrite any_dec_cons.
      rewrite H21.
      apply orb_true_r.
      rewrite H23 in H22.
      unfold randomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H24 in H22.
      simp_in_support.    
      trivial.
      rewrite H24 in H22.
      repeat simp_in_support.
      rewrite any_dec_cons.
      rewrite H21.
      apply orb_true_r.
      
      intuition.
      unfold nestedRandomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H23 in H22.
      simp_in_support.
      rewrite any_dec_cons.
      rewrite H21.
      apply orb_true_r.
      rewrite H23 in H22.
      unfold randomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H24 in H22.
      simp_in_support.    
      trivial.
      rewrite H24 in H22.
      repeat simp_in_support.
      rewrite any_dec_cons.
      rewrite H21.
      apply orb_true_r.

      intros.
      trivial.

      trivial.
      intuition idtac.
      discriminate.

      fcf_simp.
      eapply comp_spec_ret; intuition.
      simpl in *.
      intuition.
      symmetry.
      rewrite <- H23 at 1.
      repeat rewrite fst_split_map_eq.
      repeat rewrite <- any_dec_map. 
      rewrite H24.
      eapply any_dec_f_eq.
      intros.
      match goal with
      | [|- context[arrayLookup ?eqd (?a ++ ?b) ?c] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      erewrite arrayLookup_app_Some; eauto.
      repeat rewrite arrayLookup_app_None.
      simpl.
      match goal with
      | [|- context[if (if ?a then _ else _) then _ else _] ] =>
        case_eq a; intros
      end.
      trivial. 
      trivial.
      trivial.
      trivial.

      simpl in *.
      intuition.
      repeat rewrite fst_split_map_eq.
      repeat rewrite <- any_dec_map. 
      rewrite H24.
      symmetry.
      rewrite <- H23 at 1.
      repeat rewrite fst_split_map_eq.
      repeat rewrite <- any_dec_map. 
      eapply any_dec_f_eq.
      intros.
      match goal with
      | [|- context[arrayLookup ?eqd (?a ++ ?b) ?c] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      erewrite arrayLookup_app_Some; eauto.
      repeat rewrite arrayLookup_app_None.
      simpl.
      match goal with
      | [|- context[if (if ?a then _ else _) then _ else _] ] =>
        case_eq a; intros
      end.
      trivial. 
      trivial.
      trivial.
      trivial.

      fcf_simp.
      eapply comp_spec_ret; intuition idtac.

      fcf_simp.
      eapply comp_spec_ret; intuition idtac.

      fcf_simp.
      eapply comp_spec_ret; intuition idtac.

    Qed.

    (* give independent random value to adversary *)
    Definition CasKDF_IND_CPA_G5c :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret (false, false)
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret (false, false)
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret (false, false)
          | Some lsR2 =>

            [cs1, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            [kls, k, st3] <-$3 (
              cs2 <-$ rndOctetString digestLen;
              k2 <-$ rndOctetString secretLen;
              [k, st3] <-$2 (casKDF cs2
                (combine 
                  (fst (split lsR2)) 
                  (combine 
                    (combine (snd (split lsSK2)) (snd (split lsR2)))
                    (skipn (S strongKE) context)
                  )
                )) _ _ (rndHist _ _ rndRange) nil;
              k3 <-$ rndOctetString secretLen;
              ret (first (k2 :: k), k3, st3)
            );
            st2 <- (((P, R, (nth strongKE context nil)), (k_strong, cs1)), (@nil Octet));
            [b, s] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) ((k1++kls), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
            ) _ _ (nestedRandomFunc _ _ rndRange st1) nil;
            ret (b, any_dec (fun x => if (arrayLookup _ (st3 ++ st2 :: nil) x) then true else false) (fst (split s)))
          end
        end
      end.

    Theorem first_cons_eq : forall (A : Type)(a : A) ls,
      ls <> nil ->
      first (a :: ls) = a :: (first ls).

      intros.
      unfold first.
      simpl.
      destruct ls; simpl in *.
      intuition idtac.
      reflexivity.

    Qed.

    Theorem first_app_single : forall (A : Type)(a : A) ls,
      first (ls ++ (a::nil)) = ls.

      intros.
      unfold first.
      rewrite app_length.
      simpl.
      rewrite plus_comm. simpl.
      rewrite firstn_app.
      rewrite minus_diag.
      simpl.
      rewrite firstn_all.
      apply app_nil_r.

    Qed.

    Theorem casKDF_rnd_spec_h : forall ls cs,
      comp_spec (fun a b => fst a = fst b /\ 
        fst (split (snd a)) = fst (split (snd b)))
      ([k, st] <-$2 (casKDF cs ls) _ _ (rndHist _ _ rndRange) nil;
      k2 <-$ rndOctetString secretLen;
      ret (first (k2::k), last (k2::k) nil, st))
      ([k, st] <-$2 (casKDF cs ls) _ _ (rndHist _ _ rndRange) nil;
      k2 <-$ rndOctetString secretLen;
      k3 <-$ rndOctetString secretLen;
      ret (first (k2::k), k3, st)).

      intros.
      destruct (eq_nat_dec (length ls) 0).
      destruct ls; simpl in *.

      fcf_inline_first.
      fcf_simp.
      fcf_irr_r.
      eapply rndOctetString_wf.
      fcf_skip.
      eapply comp_spec_ret; intuition.
      discriminate.

      assert (exists ls' x, ls = ls' ++ x :: nil).
      exists (firstn (pred (length ls)) ls).
      exists (nth (pred (length ls)) ls (nil, (nil, nil, nil))).
      erewrite (@lsAppCons _ _ (pred (length ls))) at 1.
      cutrewrite (skipn (S (Init.Nat.pred (length ls))) ls = nil).
      reflexivity.
      destruct ls; simpl in *.
      trivial.
      eapply skipn_ge_nil.
      lia.
      destruct ls; simpl in *.
      intuition idtac.
      lia.

      destruct H.
      destruct H.
      subst.

      eapply comp_spec_eq_trans_l.
      eapply comp_spec_seq_eq;
      eauto with inhabited.
      eapply casKDF_app_spec.
      intros.
      eapply comp_spec_eq_refl.
      eapply comp_spec_symm.
      eapply comp_spec_eq_trans_l.
      eapply comp_spec_seq_eq; eauto with inhabited.
      eapply casKDF_app_spec.
      intros.
      eapply comp_spec_eq_refl.
      simpl.
      fcf_inline_first.
      fcf_skip. 
      simpl.
      fcf_inline_first.
      fcf_simp.
      simpl.
      fcf_inline_first.
      unfold rndHist.
      fcf_inline_first.
      fcf_irr_l.
      fcf_simp.
      fcf_inline_first.
      eapply comp_spec_symm.
      fcf_swap rightc.
      fcf_skip.
      eapply rndRange_skipn_spec.
      fcf_inline_first.
      simpl in *; subst.
      fcf_skip.
      eapply comp_spec_ret; intuition.  
      simpl.
      f_equal.
      repeat rewrite first_cons_eq.
      repeat rewrite first_app_single.
      reflexivity.
      intuition idtac.
      eapply app_cons_not_nil.
      symmetry; eauto.
      intuition idtac.
      eapply app_cons_not_nil.
      symmetry; eauto.

      match goal with
      | [|- context[match ?a with | nil => _ | _ :: _ => _ end ] ] =>
        case_eq a; intros
      end.
      exfalso.
      eapply app_cons_not_nil.
      symmetry; eauto.
      rewrite <- H6.
      rewrite last_app_eq.
      simpl.
      reflexivity.
      intuition idtac.
      discriminate.
    
      simpl.
      remember (split b) as z.
      destruct z.
      simpl.
      trivial.

    Qed.

    Theorem casKDF_rnd_spec : forall ls,
      comp_spec (fun a b => fst a = fst b /\ 
        fst (split (snd a)) = fst (split (snd b)))
      (cs <-$ rndOctetString digestLen;
      k2 <-$ rndOctetString secretLen;
      [k, st] <-$2 (casKDF cs ls) _ _ (rndHist _ _ rndRange) nil;
      ret (first (k2::k), last (k2::k) nil, st))
      (cs <-$ rndOctetString digestLen;
      k2 <-$ rndOctetString secretLen; 
      [k, st] <-$2 (casKDF cs ls) _ _ (rndHist _ _ rndRange) nil;
      k3 <-$ rndOctetString secretLen;
      ret (first (k2::k), k3, st)).

      intros.
      fcf_skip.
      eapply comp_spec_eq_trans_l.
      2:{
      eapply comp_spec_eq_trans_r.
      apply casKDF_rnd_spec_h.
      fcf_swap rightc.
      fcf_skip.
      }
      fcf_swap leftc.
      fcf_skip.

    Qed.

    Theorem CasKDF_IND_CPA_G5bc_eq_until_bad:
    forall a : bool,
      evalDist CasKDF_IND_CPA_G5b (a, false) ==
      evalDist CasKDF_IND_CPA_G5c (a, false).

      intros.
      eapply comp_spec_impl_eq.
      do 6 (fcf_skip; fcf_simp). 
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      do 2 (fcf_skip; fcf_simp). 
      eapply casKDF_rnd_spec.
      simpl in *; intuition; subst.
      pairInv.
      fcf_skip.
      eapply comp_spec_ret; intuition.
      pairInv.
      f_equal.
      eapply any_dec_f_eq.
      intros.
      match goal with
      | [|- context[if (arrayLookup ?eqd (?a ++ ?b) ?c) then _ else _] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      match goal with
      | [|- context[if (arrayLookup ?eqd (?a ++ ?b) ?c) then _ else _] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      eapply arrayLookup_In_split in H21.
      exfalso.
      eapply arrayLookup_None_not_In in H22.
      intuition.
      assert (forall (A : Type)(ls1 ls2 : list A)a,
        ls1 = ls2 ->
        In a ls1 -> In a ls2).
      intuition.
      subst.
      trivial.
      eapply H24.
      symmetry.
      eauto.
      trivial.
      rewrite arrayLookup_app_None; eauto.
      simpl.
      rewrite arrayLookup_app_None.
      simpl.
      match goal with
      | [|- context[if (if ?a then _ else _) then _ else _] ] =>
        case_eq a; intros
      end.
      trivial.
      trivial.
      eapply notInArrayLookupNone.
      intuition.
      eapply arrayLookup_None_not_In in H21.
      intuition.
      assert (forall (A : Type)(ls1 ls2 : list A)a,
        ls1 = ls2 ->
        In a ls1 -> In a ls2).
      intuition.
      subst.
      trivial.
      eapply H24.
      eauto.
      trivial.

      pairInv.
      f_equal.
      eapply any_dec_f_eq.
      intros.
      match goal with
      | [|- context[if (arrayLookup ?eqd (?a ++ ?b) ?c) then _ else _] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      match goal with
      | [|- context[if (arrayLookup ?eqd (?a ++ ?b) ?c) then _ else _] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      eapply arrayLookup_In_split in H21.
      exfalso.
      eapply arrayLookup_None_not_In in H22.
      intuition.
      assert (forall (A : Type)(ls1 ls2 : list A)a,
        ls1 = ls2 ->
        In a ls1 -> In a ls2).
      intuition.
      subst.
      trivial.
      eapply H24.
      eauto.
      trivial.
      rewrite arrayLookup_app_None; eauto.
      simpl.
      rewrite arrayLookup_app_None.
      simpl.
      match goal with
      | [|- context[if (if ?a then _ else _) then _ else _] ] =>
        case_eq a; intros
      end.
      trivial.
      trivial.
      eapply notInArrayLookupNone.
      intuition.
      eapply arrayLookup_None_not_In in H21.
      intuition.
      assert (forall (A : Type)(ls1 ls2 : list A)a,
        ls1 = ls2 ->
        In a ls1 -> In a ls2).
      intuition.
      subst.
      trivial.
      eapply H24.
      symmetry.
      eauto.
      trivial.

      fcf_simp.
      eapply comp_spec_ret; intuition.
      fcf_simp.
      eapply comp_spec_ret; intuition.
      eapply comp_spec_ret; intuition.

    Qed.

    Theorem CasKDF_IND_CPA_G5bc_bad_same :
      Pr[x <-$ CasKDF_IND_CPA_G5b; ret snd x] ==
      Pr[x <-$ CasKDF_IND_CPA_G5c; ret snd x].

      intros.
      unfold CasKDF_IND_CPA_G5b, CasKDF_IND_CPA_G5c.
      eapply comp_spec_eq_impl_eq.
      eapply comp_spec_seq_eq; eauto with inhabited.
      do 6 (fcf_skip; fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      do 2 (fcf_skip; fcf_simp).
      eapply casKDF_rnd_spec.
      simpl in *; intuition; subst.
      pairInv.
      fcf_skip.

      eapply comp_spec_ret; intuition.
      f_equal.
      eapply any_dec_f_eq.
      intros.
      match goal with
      | [|- context[if (arrayLookup ?eqd (?a ++ ?b) ?c) then _ else _] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      match goal with
      | [|- context[if (arrayLookup ?eqd (?a ++ ?b) ?c) then _ else _] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      eapply arrayLookup_In_split in H21.
      exfalso.
      eapply arrayLookup_None_not_In in H22.
      intuition.

      assert (forall (A : Type)(ls1 ls2 : list A)a,
        ls1 = ls2 ->
        In a ls1 -> In a ls2).
      intuition.
      subst.
      trivial.
      eapply H23.
      eauto.
      trivial.
      rewrite arrayLookup_app_None; eauto.
      simpl.
      rewrite arrayLookup_app_None.
      simpl.
      match goal with
      | [|- context[if (if ?a then _ else _) then _ else _] ] =>
        case_eq a; intros
      end.
      trivial.
      trivial.
      eapply notInArrayLookupNone.
      intuition.
      eapply arrayLookup_None_not_In in H21.
      intuition.
      assert (forall (A : Type)(ls1 ls2 : list A)a,
        ls1 = ls2 ->
        In a ls1 -> In a ls2).
      intuition.
      subst.
      trivial.
      eapply H23.
      symmetry.
      eauto.
      trivial.

      intuition.

      fcf_simp.
      eapply comp_spec_ret; intuition.

      fcf_simp.
      eapply comp_spec_ret; intuition.

      intros.
      eapply comp_spec_ret; intuition.

    Qed.

    (* put additional information back in nested random function *)
    Definition CasKDF_IND_CPA_G5d :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret (false, false)
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret (false, false)
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret (false, false)
          | Some lsR2 =>
            [cs1, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            cs2 <-$ rndOctetString digestLen;
            k2 <-$ rndOctetString secretLen;
            st2 <- (((P, R, (nth strongKE context nil)), (k_strong, cs1)), (cs2 ++ k2));
            [k3, st3] <-$2 (casKDF cs2
              (combine 
                (fst (split lsR2)) 
                (combine 
                  (combine (snd (split lsSK2)) (snd (split lsR2)))
                  (skipn (S strongKE) context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            k <-$ rndOctetString secretLen;
            [b, s] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k3), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
            ) _ _ (nestedRandomFunc _ _ rndRange (st3 ++ st2::st1)) nil;
            ret (b, any_dec (fun x => if (arrayLookup _ (st3 ++ st2 :: nil) x) then true else false) (fst (split s)))
          end
        end
      end.

    Theorem CasKDF_IND_CPA_G5cd_eq_until_bad : forall x,
      evalDist CasKDF_IND_CPA_G5c (x, false) == evalDist CasKDF_IND_CPA_G5d (x, false).

      unfold CasKDF_IND_CPA_G5c, CasKDF_IND_CPA_G5d.
      intros.
      symmetry.
      eapply comp_spec_impl_eq.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      rewrite first_app_eq.
      eapply (fcf_oracle_eq_until_bad 
        (any_dec (fun y => if (arrayLookup _ 
          (b8 ++
         (b, o0, nth strongKE context nil,
         (o, a), (b0 ++ b7)) :: nil) (fst y)) then true else false))
        (any_dec (fun y => if (arrayLookup _ 
          (b8 ++
         (b, o0, nth strongKE context nil,
         (o, a), (b0 ++ b7)) :: nil) (fst y)) then true else false))
        (fun x y => forall z, arrayLookup _ x z = arrayLookup _ y z)
      ).
      trivial.
      intros.
      eapply nestedRandomFunc_wf.
      eapply rndOctetString_wf.
      intros.
      eapply nestedRandomFunc_wf.
      eapply rndOctetString_wf.
      intros.

      rewrite (app_cons_eq _ b5).
      eapply comp_spec_consequence.
      eapply nestedRandomFunc_app_spec.
      eapply rndOctetString_wf.

      intuition.
      intuition.
      intuition.

      unfold nestedRandomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H25 in H24.
      simp_in_support.
      rewrite any_dec_cons.
      rewrite H23.
      apply orb_true_r.
      rewrite H25 in H24.
      unfold randomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H26 in H24.
      simp_in_support.    
      trivial.
      rewrite H26 in H24.
      repeat simp_in_support.
      rewrite any_dec_cons.
      rewrite H23.
      apply orb_true_r.
      
      intuition.
      unfold nestedRandomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H25 in H24.
      simp_in_support.
      rewrite any_dec_cons.
      rewrite H23.
      apply orb_true_r.
      rewrite H25 in H24.
      unfold randomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H26 in H24.
      simp_in_support.    
      trivial.
      rewrite H26 in H24.
      repeat simp_in_support.
      rewrite any_dec_cons.
      rewrite H23.
      apply orb_true_r.

      intros.
      trivial.

      trivial.
      intuition idtac.
      discriminate.

      eapply comp_spec_ret; intuition.
      pairInv.
      simpl in *.
      rewrite fst_split_map_eq in H29.
      rewrite <- any_dec_map in H29.
      intuition.
      subst.
      f_equal.
      rewrite fst_split_map_eq.
      rewrite <- any_dec_map.
      rewrite H29.
      rewrite fst_split_map_eq.
      rewrite <- any_dec_map.
      symmetry.
      rewrite <- H29 at 1.
      rewrite H26.
      eapply any_dec_f_eq.
      intros.
      match goal with
      | [|- context[arrayLookup ?eqd (?a ++ ?b) ?c] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      erewrite arrayLookup_app_Some; eauto.
      repeat rewrite arrayLookup_app_None.
      simpl.
      match goal with
      | [|- context[if (if ?a then _ else _) then _ else _] ] =>
        case_eq a; intros
      end.
      trivial. 
      trivial.
      trivial.
      trivial.

      pairInv.
      simpl in *.
      rewrite fst_split_map_eq in H29.
      rewrite <- any_dec_map in H29.
      match goal with
      | [H: ?a -> _ |- _] =>
        cut a
      end; intuition.
      subst.
      
      f_equal.
      eapply H28.
      rewrite H27.
      symmetry.
      rewrite <- H29 at 1.
      eapply any_dec_f_eq.
      intros.
      match goal with
      | [|- context[ if ?a then _ else _] ] => 
        case_eq a; intros
      end.
      match goal with
      | [|- context[ if ?a then _ else _] ] => 
        case_eq a; intros
      end.
      trivial.
      apply arrayLookup_In_split in H30.
      simpl in *.
      eapply arrayLookup_None_not_In in H31.
      intuition.
      rewrite fst_split_app.
      rewrite fst_split_app in *.
      simpl in *.
      trivial.
      match goal with
      | [|- context[ if ?a then _ else _] ] => 
        case_eq a; intros
      end.
      apply arrayLookup_In_split in H31.
      simpl in *.
      eapply arrayLookup_None_not_In in H30.
      intuition.
      rewrite fst_split_app.
      rewrite fst_split_app in *.
      simpl in *.
      trivial.
      trivial. 
      
      rewrite fst_split_map_eq.
      rewrite <- any_dec_map.
      symmetry.
      rewrite fst_split_map_eq.
      rewrite <- any_dec_map.
      transitivity (any_dec
        (fun y : DomainRO * list (Bvector 8) =>
         if
          arrayLookup
            (pair_EqDec
               (pair_EqDec
                  (pair_EqDec (list_EqDec (Bvector_EqDec 8))
                     (list_EqDec (Bvector_EqDec 8)))
                  (list_EqDec (Bvector_EqDec 8)))
               (pair_EqDec (list_EqDec (Bvector_EqDec 8))
                  (list_EqDec (Bvector_EqDec 8))))
            (b8 ++
             (b, o0, nth strongKE context nil, 
             (o, a), b0 ++ b7) :: nil) (fst y)
         then true
         else false) l1).
      eapply any_dec_f_eq.
      intros.
      match goal with
      | [|- context[ if ?a then _ else _] ] => 
        case_eq a; intros
      end.
      match goal with
      | [|- context[ if ?a then _ else _] ] => 
        case_eq a; intros
      end.
      trivial.
      apply arrayLookup_In_split in H30.
      simpl in *.
      eapply arrayLookup_None_not_In in H31.
      intuition.
      rewrite fst_split_app.
      rewrite fst_split_app in *.
      simpl in *.
      trivial.
      match goal with
      | [|- context[ if ?a then _ else _] ] => 
        case_eq a; intros
      end.
      apply arrayLookup_In_split in H31.
      simpl in *.
      eapply arrayLookup_None_not_In in H30.
      intuition.
      rewrite fst_split_app.
      rewrite fst_split_app in *.
      simpl in *.
      trivial.
      trivial. 
      
      rewrite <- H27 at 1.
      eapply any_dec_f_eq.
      intros.
      match goal with
      | [|- context[arrayLookup ?eqd (?a ++ ?b) ?c] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      repeat rewrite arrayLookup_app_None; eauto.
      simpl.
      match goal with
      | [|- context[if (if ?a then _ else _) then _ else _] ] =>
        case_eq a; intros
      end.
      trivial.
      symmetry.
      trivial.

      fcf_simp.
      eapply comp_spec_ret; intuition.
      
      fcf_simp.
      eapply comp_spec_ret; intuition.
      
      eapply comp_spec_ret; intuition.

    Qed.

    Theorem CasKDF_IND_CPA_G5cd_bad_same : 
      Pr[x <-$ CasKDF_IND_CPA_G5c; ret (snd x)] == Pr[x <-$ CasKDF_IND_CPA_G5d; ret (snd x)].

      unfold CasKDF_IND_CPA_G5c, CasKDF_IND_CPA_G5d.
      intros.
      symmetry.
      eapply comp_spec_impl_eq.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp). 
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp). 

      rewrite first_app_eq.
      eapply (fcf_oracle_eq_until_bad 
        (any_dec (fun y => if (arrayLookup _ 
          (b8 ++
         (b, o0, nth strongKE context nil,
         (o, a), b0++b7) :: nil) (fst y)) then true else false))
        (any_dec (fun y => if (arrayLookup _ 
          (b8 ++
         (b, o0, nth strongKE context nil,
         (o, a), b0++b7) :: nil) (fst y)) then true else false))
        (fun x y => forall z, arrayLookup _ x z = arrayLookup _ y z)
      ).
      trivial.
      intros.
      eapply nestedRandomFunc_wf.
      eapply rndOctetString_wf.
      intros.
      eapply nestedRandomFunc_wf.
      eapply rndOctetString_wf.
      intros.

      rewrite (app_cons_eq _ b5).
      eapply comp_spec_consequence.
      eapply nestedRandomFunc_app_spec.
      eapply rndOctetString_wf.

      intuition.
      intuition.
      intuition.

      unfold nestedRandomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H25 in H24.
      simp_in_support.
      rewrite any_dec_cons.
      rewrite H23.
      apply orb_true_r.
      rewrite H25 in H24.
      unfold randomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H26 in H24.
      simp_in_support.    
      trivial.
      rewrite H26 in H24.
      repeat simp_in_support.
      rewrite any_dec_cons.
      rewrite H23.
      apply orb_true_r.
      
      intuition.
      unfold nestedRandomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H25 in H24.
      simp_in_support.
      rewrite any_dec_cons.
      rewrite H23.
      apply orb_true_r.
      rewrite H25 in H24.
      unfold randomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _] =>
        case_eq a; intros
      end.
      rewrite H26 in H24.
      simp_in_support.    
      trivial.
      rewrite H26 in H24.
      repeat simp_in_support.
      rewrite any_dec_cons.
      rewrite H23.
      apply orb_true_r.

      intros.
      trivial.

      trivial.
      intuition idtac.
      discriminate.

      eapply comp_spec_ret; intuition.
      simpl in *.
      intuition.
      symmetry.
      rewrite <- H26 at 1.
      repeat rewrite fst_split_map_eq.
      repeat rewrite <- any_dec_map. 
      rewrite H27.
      eapply any_dec_f_eq.
      intros.
      match goal with
      | [|- context[arrayLookup ?eqd (?a ++ ?b) ?c] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      erewrite arrayLookup_app_Some; eauto.
      repeat rewrite arrayLookup_app_None; eauto.
      simpl.
      match goal with
      | [|- context[if (if ?a then _ else _) then _ else _] ] =>
        case_eq a; intros
      end.
      trivial. 
      trivial.

      simpl in *.
      intuition.
      repeat rewrite fst_split_map_eq.
      repeat rewrite <- any_dec_map. 
      rewrite H27.
      symmetry.
      rewrite <- H26 at 1.
      repeat rewrite fst_split_map_eq.
      repeat rewrite <- any_dec_map. 
      eapply any_dec_f_eq.
      intros.
      match goal with
      | [|- context[arrayLookup ?eqd (?a ++ ?b) ?c] ] =>
        case_eq (arrayLookup eqd a c); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      erewrite arrayLookup_app_Some; eauto.
      repeat rewrite arrayLookup_app_None; eauto.
      simpl.
      match goal with
      | [|- context[if (if ?a then _ else _) then _ else _] ] =>
        case_eq a; intros
      end.
      trivial. 
      trivial.

      fcf_simp.
      eapply comp_spec_ret; intuition.
      fcf_simp.
      eapply comp_spec_ret; intuition.
      fcf_simp.
      eapply comp_spec_ret; intuition.

    Qed.


    Theorem CasKDF_IND_CPA_G5d_G6_equiv : 
      Pr[x <-$ CasKDF_IND_CPA_G5d; ret (fst x)] == Pr[CasKDF_IND_CPA_G6].

      unfold CasKDF_IND_CPA_G5d, CasKDF_IND_CPA_G6.
      eapply comp_spec_eq_impl_eq.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).

      eapply comp_spec_symm.
      eapply (fcf_oracle_eq (nestedRandomFunc_pred _ 
        (b8 ++
   (b, o0, nth strongKE context nil,
   (o, a), (b0++b7))::b5))).
      unfold nestedRandomFunc_pred.
      intuition.
      rewrite app_nil_r.
      reflexivity.
      intuition.
      eapply nestedRandomFunc_spec.
      trivial.
      simpl in *.
      intuition. subst.
      eapply comp_spec_eq_refl.

      fcf_simp.
      eapply comp_spec_ret; intuition.
      fcf_simp.
      eapply comp_spec_ret; intuition.
      fcf_simp.
      eapply comp_spec_ret; intuition.

    Qed.

    Definition CasKDF_IND_CPA_G6_bad1 :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret false
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret false
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret false
          | Some lsR2 =>
            [cs1, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            cs2 <-$ rndOctetString digestLen;
            k2 <-$ rndOctetString secretLen;
            st2 <- (((P, R, (nth strongKE context nil)), (k_strong, cs1)), (@nil Octet));
            [k3, st3] <-$2 (casKDF cs2
              (combine 
                (fst (split lsR2)) 
                (combine 
                  (combine (snd (split lsSK2)) (snd (split lsR2)))
                  (skipn (S strongKE) context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            k <-$ rndOctetString secretLen;
            [_, s] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k3), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
            ) _ _ (nestedRandomFunc _ _ rndRange st1) nil;
            ret (any_dec (fun x => if (arrayLookup _ (st3 ++ st2 :: nil) x) then true else false) (fst (split s)))
          end
        end
      end.

    Theorem CasKDF_IND_CPA_G6_bad1_equiv : 
      Pr[x <-$ CasKDF_IND_CPA_G5c; ret (snd x)] == Pr[CasKDF_IND_CPA_G6_bad1].

      unfold CasKDF_IND_CPA_G5c, CasKDF_IND_CPA_G6_bad1.

      do 6 (
      fcf_inline_first;
      fcf_skip;
      fcf_simp).

      destOpt.
      destOpt.
      destOpt.
      fcf_simp.

      do 6 (
      fcf_inline_first;
      fcf_skip;
      fcf_simp).

      rewrite first_app_eq.
      reflexivity.
      intuition idtac.
      discriminate.
      eapply evalDist_ret_eq. 
      rewrite any_dec_arrayLookup_swap.
      symmetry.
      rewrite any_dec_arrayLookup_swap.
      repeat rewrite fst_split_app.
      simpl.
      eapply any_dec_f_eq.
      intuition.

      fcf_simp.
      reflexivity.
    
      fcf_simp.
      reflexivity.
      
      fcf_simp.
      reflexivity.
 
    Qed.

    Theorem CasKDF_IND_CPA_G6_close_bad : 
      | Pr[CasKDF_IND_CPA_G5 A] - Pr[CasKDF_IND_CPA_G6] | <= Pr[CasKDF_IND_CPA_G6_bad1].
      
      rewrite CasKDF_IND_CPA_G5a_equiv.
      rewrite <- CasKDF_IND_CPA_G5d_G6_equiv.
      rewrite fundamental_lemma_h.
      rewrite CasKDF_IND_CPA_G5ab_bad_same.
      rewrite CasKDF_IND_CPA_G5bc_bad_same.
      rewrite CasKDF_IND_CPA_G6_bad1_equiv.
      reflexivity.

      rewrite CasKDF_IND_CPA_G5ab_bad_same.
      rewrite CasKDF_IND_CPA_G5bc_bad_same.
      eapply CasKDF_IND_CPA_G5cd_bad_same.

      intros.
      rewrite CasKDF_IND_CPA_G5ab_eq_until_bad.
      rewrite CasKDF_IND_CPA_G5bc_eq_until_bad.
      eapply CasKDF_IND_CPA_G5cd_eq_until_bad.
    Qed.

    (* split the last game into a sum of two events.*)
    Definition CasKDF_IND_CPA_G6_bad2 :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret false
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret false
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret false
          | Some lsR2 =>
            [cs1, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            cs2 <-$ rndOctetString digestLen;
            k2 <-$ rndOctetString secretLen;
            [k3, st3] <-$2 (casKDF cs2
              (combine 
                (fst (split lsR2)) 
                (combine 
                  (combine (snd (split lsSK2)) (snd (split lsR2)))
                  (skipn (S strongKE) context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            k <-$ rndOctetString secretLen;
            [_, s] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k3), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
            ) _ _ (nestedRandomFunc _ _ rndRange st1) nil;
            ret (if (arrayLookup _ s ((P, R, (nth strongKE context nil)), (k_strong, cs1))) then true else false) ||
                any_dec (fun x => if (arrayLookup _ st3 x) then true else false) (fst (split s))
          end
        end
      end.


    Theorem CasKDF_IND_CPA_G6_bad2_le : 
      Pr[CasKDF_IND_CPA_G6_bad1] <= Pr[CasKDF_IND_CPA_G6_bad2].

      unfold CasKDF_IND_CPA_G6_bad1, CasKDF_IND_CPA_G6_bad2.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      eapply comp_spec_impl_le.
      eapply comp_spec_ret; intuition.
      rewrite any_dec_arrayLookup_swap in H13.
      rewrite fst_split_app in H13.
      rewrite any_dec_app in H13.
      eapply orb_true_elim in H13.
      intuition.
      rewrite any_dec_arrayLookup_swap in a.
      rewrite a.
      eapply orb_true_r.

      fcf_simp.
      reflexivity.
      fcf_simp.
      reflexivity.
      fcf_simp.
      reflexivity.
      
    Qed.

    (* The first event is the violation of OW-CPA *)
    Definition CasKDF_IND_CPA_G6_bad_a1 :=
      [_, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret false
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret false
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret false
          | Some lsR2 =>
            [cs1, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            cs2 <-$ rndOctetString digestLen;
            k2 <-$ rndOctetString secretLen;
            [k3, st3] <-$2 (casKDF cs2
              (combine 
                (fst (split lsR2)) 
                (combine 
                  (combine (snd (split lsSK2)) (snd (split lsR2)))
                  (skipn (S strongKE) context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            k <-$ rndOctetString secretLen;
            [_, s] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k3), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
            ) _ _ (nestedRandomFunc _ _ rndRange st1) nil;
            ret (if (arrayLookup _ s ((P, R, (nth strongKE context nil)), (k_strong, cs1))) then true else false)
          end
        end
      end.

    (* use regular random function so nested random function doesn't appear in constructed adversary *)
    Definition CasKDF_IND_CPA_G6_bad_a2 :=
      [_, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret false
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret false
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret false
          | Some lsR2 =>
            [cs1, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            cs2 <-$ rndOctetString digestLen;
            k2 <-$ rndOctetString secretLen;
            [k3, st3] <-$2 (casKDF cs2
              (combine 
                (fst (split lsR2)) 
                (combine 
                  (combine (snd (split lsSK2)) (snd (split lsR2)))
                  (skipn (S strongKE) context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            k <-$ rndOctetString secretLen;
            [_, s] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k3), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
            ) _ _ (randomFunc rndRange _) st1;
            ret (if (arrayLookup _ s ((P, R, (nth strongKE context nil)), (k_strong, cs1))) then true else false)
          end
        end
      end.

    Theorem CasKDF_IND_CPA_G6_bad_a2_equiv : 
      Pr[CasKDF_IND_CPA_G6_bad_a1] <= Pr[CasKDF_IND_CPA_G6_bad_a2].

      unfold CasKDF_IND_CPA_G6_bad_a1, CasKDF_IND_CPA_G6_bad_a2.
      eapply comp_spec_impl_le.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      destOpt. 
      destOpt.
      destOpt.
      fcf_simp.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      eapply comp_spec_symm.
      eapply (fcf_oracle_eq (nestedRandomFunc_pred _ 
        b5)).
      unfold nestedRandomFunc_pred.
      intuition.
      rewrite app_nil_r.
      reflexivity.
      intuition.
      eapply nestedRandomFunc_spec.
      trivial.
      simpl in *; intuition; subst.
      eapply comp_spec_ret; intuition.
      unfold nestedRandomFunc_pred in *.
      rewrite H27.
      match goal with
      | [|- context[ if (arrayLookup ?eqd (?ls1 ++ ?ls2) ?a) then _ else _] ] =>
        case_eq (arrayLookup eqd ls1 a); intros
      end.
      erewrite arrayLookup_app_Some; eauto.
      rewrite arrayLookup_app_None.
      trivial.
      trivial.

      fcf_simp.
      eapply comp_spec_ret; intuition idtac.
      fcf_simp.
      eapply comp_spec_ret; intuition idtac.
      eapply comp_spec_ret; intuition idtac.
      
    Qed.

    Definition strongKE_A P R :=
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
          [k1, st1] <-$2 (casKDF psk
            (combine 
              (fst (split lsR1)) 
              (combine 
                (combine (snd (split lsSK1)) (snd (split lsR1)))
                (firstn strongKE context)
              )
            )) _ _ (rndHist _ _ rndRange) nil;
          cs2 <-$ rndOctetString digestLen;
          k2 <-$ rndOctetString secretLen;
          [k3, st3] <-$2 (casKDF cs2
            (combine 
              (fst (split lsR2)) 
              (combine 
                (combine (snd (split lsSK2)) (snd (split lsR2)))
                (skipn (S strongKE) context)
              )
            )) _ _ (rndHist _ _ rndRange) nil;
          k <-$ rndOctetString secretLen;
          [_, s] <-$2 (
            (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k3), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
          ) _ _ (randomFunc rndRange _) st1;
          ret (fst (split s))
        end
      end.

    Theorem casKDF_cs_spec : forall ps k (S : Set)(eqds : EqDec S)(s : S) o,
      comp_spec (fun a b => snd a = snd b /\ snd (fst a) = fst b) 
        ((casKDF_cs k ps) _ _ o s) ((casKDF k ps) _ _ o s).

      induction ps; intuition; simpl in *.
      fcf_simp.
      eapply comp_spec_ret; intuition.
      fcf_skip.
      fcf_skip.
      fcf_simp.
      eapply comp_spec_ret; intuition.
      simpl in *; subst.
      trivial.

    Qed.

    Theorem CasKDF_IND_CPA_G6_bad_a2_OW_CPA_equiv : 
      Pr[CasKDF_IND_CPA_G6_bad_a2] <= 
      (@KeyExchangeOW_CPA_List_Advantage _ _ _ _ _ _ _ (nth strongKE KE defKE) (fun q p => eqb q (fst (snd p))) strongKE_A).

      eapply comp_spec_impl_le.

      unfold CasKDF_IND_CPA_G6_bad_a1, KeyExchangeOW_CPA_List_Advantage, strongKE_A.

      fcf_skip.
      fcf_skip.
      simpl.
      destOpt.
      fcf_simp.
      do 4(
      fcf_inline_first;
      fcf_skip;
      fcf_simp).
      destOpt.
      destOpt.
      fcf_inline_first. fcf_skip.
      eapply casKDF_cs_spec.
      simpl in *; subst.
      fcf_simp.
      do 5(
      fcf_inline_first;
      fcf_skip;
      fcf_simp).

      eapply comp_spec_ret; intuition.
      match goal with
      | [H: context[if ?a then _ else _] |- _] =>
        case_eq a; intros
      end.
      apply arrayLookup_Some_impl_In in H26.
      eapply any_dec_true_ex.
      econstructor.
      intuition.
      eapply in_split_l.
      eauto.
      simpl.
      apply eqb_refl.
      rewrite H26 in H25.
      discriminate.

      fcf_simp.
      eapply comp_spec_ret; intuition idtac.
      fcf_simp.
      eapply comp_spec_ret; intuition idtac.

      subst.
      fcf_irr_l.
      eapply list_EqDec.
      eapply pair_EqDec;
      eapply OctetString_EqDec.
      eapply compMap_wf; intros.
      eapply keyGen_wf.
      eapply firstn_In; eauto.
      fcf_irr_l.
      eapply list_EqDec.
      eapply pair_EqDec;
      eapply OctetString_EqDec.
      eapply compMap_wf; intros.
      destruct KE.
      simpl in *. intuition idtac.
      eapply keyGen_wf.
      simpl.
      right.
      eapply skipn_In; eauto.

      fcf_irr_l.
      eapply list_EqDec.
      eapply option_EqDec.
      eapply pair_EqDec;
      eapply OctetString_EqDec.
      eapply compMap_wf; intros.
      eapply responseFunc_wf.
      destruct a2. simpl.
      eapply firstn_In.
      eapply in_combine_l; eauto.

      fcf_irr_l.  
      eapply list_EqDec.
      eapply option_EqDec.
      eapply pair_EqDec;
      eapply OctetString_EqDec.
      eapply compMap_wf; intros.
      destruct KE; simpl in *.
      intuition idtac.
      eapply responseFunc_wf.
      right.
      destruct a3; simpl in *.
      eapply skipn_In.
      eapply in_combine_l; eauto.
      eapply comp_spec_ret; intuition.
    Qed.

    (* second event is the adversary queries on random values produced in second part of cascade *)
    Definition CasKDF_IND_CPA_G6_bad_b1 :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret false
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret false
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret false
          | Some lsR2 =>
            [_, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            cs2 <-$ rndOctetString digestLen;
            k2 <-$ rndOctetString secretLen;
            [k3, st3] <-$2 (casKDF cs2
              (combine 
                (fst (split lsR2)) 
                (combine 
                  (combine (snd (split lsSK2)) (snd (split lsR2)))
                  (skipn (S strongKE) context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            k <-$ rndOctetString secretLen;
            [_, s] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k3), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
            ) _ _ (nestedRandomFunc _ _ rndRange st1) nil;
            ret (any_dec (fun x => if (arrayLookup _ st3 x) then true else false) (fst (split s)))
          end
        end
      end.

    Definition CasKDF_IND_CPA_G6_bad2a :=
      z <-$ (
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret (((nil, nil, nil), (nil, nil)), nil, nil)
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret (((nil, nil, nil), (nil, nil)), nil, nil)
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret (((nil, nil, nil), (nil, nil)), nil, nil)
          | Some lsR2 =>
            [cs1, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            cs2 <-$ rndOctetString digestLen;
            k2 <-$ rndOctetString secretLen;
            [k3, st3] <-$2 (casKDF cs2
              (combine 
                (fst (split lsR2)) 
                (combine 
                  (combine (snd (split lsSK2)) (snd (split lsR2)))
                  (skipn (S strongKE) context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            k <-$ rndOctetString secretLen;
            [_, s] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k3), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
            ) _ _ (nestedRandomFunc _ _ rndRange st1) nil;
            ret (((P, R, (nth strongKE context nil)), (k_strong, cs1)), s, st3)
          end
        end
      end
      );
      ret (if (arrayLookup _ (snd (fst z)) (fst (fst z))) then true else false) ||
          any_dec (fun x => if (arrayLookup _ (snd z) x) then true else false) (fst (split (snd (fst z)))).

    Theorem CasKDF_IND_CPA_G6_bad2a_equiv :   
      Pr[CasKDF_IND_CPA_G6_bad2] == Pr[CasKDF_IND_CPA_G6_bad2a].

      unfold CasKDF_IND_CPA_G6_bad2, CasKDF_IND_CPA_G6_bad2a.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      reflexivity.

      fcf_simp.
      simpl.
      fcf_compute.

      fcf_simp.
      simpl.
      fcf_compute.

      fcf_simp.
      simpl.
      fcf_compute.
    Qed.

    Theorem CasKDF_IND_CPA_G6_bad2_split : 
      Pr[CasKDF_IND_CPA_G6_bad2] <= Pr[CasKDF_IND_CPA_G6_bad_a1] + Pr[CasKDF_IND_CPA_G6_bad_b1].

      rewrite CasKDF_IND_CPA_G6_bad2a_equiv.
      unfold CasKDF_IND_CPA_G6_bad2a, CasKDF_IND_CPA_G6_bad_a1, CasKDF_IND_CPA_G6_bad_b1.
      rewrite evalDist_orb_le.
      eapply ratAdd_leRat_compat.

      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      simpl.  
      reflexivity.

      fcf_simp.
      reflexivity.
      fcf_simp.
      reflexivity.
      fcf_simp.
      reflexivity.

      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      simpl.  
      reflexivity.

      fcf_simp.
      reflexivity.
      fcf_simp.
      reflexivity.
      fcf_simp.
      reflexivity.
    Qed.

    (* (inequality) The adversary wins if any of the chain secrets are in any queries *)
    Definition CasKDF_IND_CPA_G6_bad_b2 :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret false
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret false
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret false
          | Some lsR2 =>
            [_, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            k2 <-$ rndOctetString secretLen;
            cs3 <-$ compMap _ (fun _ => rndOctetString digestLen) (forNats (length KE - strongKE));
            k3 <-$ compMap _ (fun _ => rndOctetString secretLen) (forNats (length KE - S strongKE));
            k <-$ rndOctetString secretLen;
            [_, s] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k3), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
            ) _ _ (nestedRandomFunc _ _ rndRange st1) nil;
            ret (any_dec (fun x => if (in_dec (EqDec_dec _) (snd (snd x)) cs3) then true else false) (fst (split s)))
          end
        end
      end.

    (* replace casKDF with simpler function that produces two random lists *)
    Fixpoint casKDF_rnd(n : nat) : Comp (list OctetString * list OctetString) :=
    match n with
    | 0 => ret (nil, nil)
    | S n' => 
        cs <-$ rndOctetString digestLen;
        k <-$ rndOctetString secretLen; 
        [k', cs'] <-$2 casKDF_rnd n'; 
        ret (k::k', cs' ++ (cs :: nil))
    end.

    Theorem casKDF_rndHist_casKDF_rnd_spec : forall n ls1 k ls2 eqd1 eqd2 eqd3,
      length ls1 = n ->
      comp_spec (fun a b => fst a = fst b /\ skipn n (snd a) = ls2 /\ Forall2 (fun x y => (firstn digestLen (snd x)) = y) (firstn n (snd a)) (snd b))
      ((casKDF k ls1) _ eqd1 (rndHist eqd2 eqd3 rndRange) ls2)
      (casKDF_rnd n).

      Local Opaque firstn skipn.

      induction n; destruct ls1; intuition; simpl in *.
      fcf_simp.
      eapply comp_spec_ret; intuition.


      lia.
      lia.
      
      unfold rndHist.
      fcf_inline_first.
      eapply comp_spec_eq_trans_l.
      eapply eq_impl_comp_spec_eq.
      intros.
      eapply evalDist_seq_eq_trans;
      eauto with inhabited.
      eapply rndOctetString_app_eq.
      fcf_inline_first; fcf_skip; fcf_simp.
      fcf_inline_first; fcf_skip; fcf_simp.
      fcf_inline_first; fcf_skip; fcf_simp.
      eapply IHn.
      lia.

      simpl in *; intuition; subst.
      eapply comp_spec_ret; intuition.
      simpl.
      apply compMap_length in H1.
      rewrite forNats_length in H1.
      rewrite <- H1.
      rewrite skipn_app.
      trivial.
   
      rewrite <- tl_skipn_eq.
      simpl.
      rewrite H6.
      reflexivity.

      simpl in *.
      intuition.
      assert ((firstn (S n) b2) = 
        (firstn n b2 ++ (firstn 1 (skipn n b2)))).
      eapply firstn_S_app.
      rewrite H7.
      eapply Forall2_app.
      trivial.
      rewrite H6.
    
      Local Transparent firstn skipn.
      simpl.
      econstructor.
      simpl.
      apply compMap_length in H0.
      rewrite forNats_length in H0.
      rewrite <- H0.
      rewrite firstn_app_eq.
      trivial.
      econstructor.
    Qed.

    Definition CasKDF_IND_CPA_G6_bad_b1a :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret false
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret false
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret false
          | Some lsR2 =>
            [_, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            cs2 <-$ rndOctetString digestLen;
            k2 <-$ rndOctetString secretLen;
            [k3, cs3] <-$2 casKDF_rnd (length KE - S strongKE);
            k <-$ rndOctetString secretLen;
            [_, s] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k3), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
            ) _ _ (nestedRandomFunc _ _ rndRange st1) nil;
            ret (any_dec (fun x => if (in_dec (EqDec_dec _) (snd (snd x)) (cs3++cs2::nil)) then true else false) (fst (split s)))
          end
        end
      end.

    Theorem In_leibniz : forall (A : Type)(ls1 ls2 : list A) a,
      ls1 = ls2 ->
      In a ls1 ->
      In a ls2.

      intuition; subst; trivial.

    Qed.

    Theorem snd_split_map_eq : forall (A B : Type)(ls : list (A * B)),
      snd (split ls) = map snd ls.

      induction ls; intuition; simpl in *.
      remember (split ls) as z. destruct z.
      simpl in *.
      f_equal.
      eauto.

    Qed.

    Theorem casKDF_rndHist_casKDF_rnd_spec_In : forall n ls1 k eqd1 eqd2 eqd3,
      length ls1 = n ->
      comp_spec (fun a b => fst a = fst b /\
        forall x, In x (map (fun y => snd (snd y)) (fst (split (snd a)))) -> In x (tl ((snd b) ++ k::nil)) 
      )
      ((casKDF k ls1) _ eqd1 (rndHist eqd2 eqd3 rndRange) nil)
      (casKDF_rnd n).

      intuition.
      eapply comp_spec_consequence_support.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply pair_EqDec; eauto with typeclass_instances.
      eapply casKDF_rndHist_casKDF_rnd_spec.
      trivial.
      intuition.
      simpl in *; subst.

      apply casKDF_support_eq in H0.
      intuition.
      eapply Forall2_map_eq in H5.
      rewrite map_id in H5.
      destruct b0; simpl in *.
      subst.
      rewrite snd_split_map_eq in H3.
      rewrite map_map in H3.
      eapply In_leibniz.
      symmetry.
      eauto.
      rewrite firstn_all2.
      trivial.
      rewrite map_length.
      rewrite split_length_l.
      eapply skipn_nil_impl_short; eauto.
      
    Qed.

    Theorem CasKDF_IND_CPA_G6_bad_b1a_le : 
      Pr[CasKDF_IND_CPA_G6_bad_b1] <= Pr[CasKDF_IND_CPA_G6_bad_b1a].

      unfold CasKDF_IND_CPA_G6_bad_b1, CasKDF_IND_CPA_G6_bad_b1a.
      eapply comp_spec_impl_le.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      fcf_inline_first; fcf_skip; fcf_simp.
      fcf_inline_first; fcf_skip; fcf_simp.
      fcf_inline_first; fcf_skip; fcf_simp.
      fcf_inline_first; fcf_skip; fcf_simp.
      eapply casKDF_rndHist_casKDF_rnd_spec_In.

      apply compMap_length in H6.
      rewrite skipn_length in H6.
      apply compMap_length in H10.
      rewrite combine_length in H10.
      rewrite min_l in H10.
      rewrite skipn_length in H10.
      rewrite combine_length.
      rewrite min_l.
      rewrite split_length_l.
      apply stripOpt_length in H13.
      congruence.
      rewrite split_length_l.
      rewrite combine_length.
      rewrite min_l.
      rewrite combine_length.
      rewrite min_l.
      rewrite split_length_r.
      apply stripOpt_length in H13.
      lia.
      repeat rewrite split_length_r.
      apply stripOpt_length in H13.
      lia.
      rewrite combine_length.
      rewrite min_l.
      rewrite split_length_r.
      rewrite skipn_length.
      apply stripOpt_length in H13.
      lia.
      rewrite split_length_r.
      rewrite split_length_r.
      apply stripOpt_length in H13.
      lia.
      rewrite skipn_length.
      rewrite split_length_r.
      lia.

      simpl in *. intuition. subst.
      fcf_inline_first; fcf_skip; fcf_simp.
      fcf_inline_first; fcf_skip; fcf_simp.
      eapply comp_spec_ret; intuition.
      eapply any_dec_ex in H26.
      dest; intuition.
      eapply ex_any_dec.
      eauto.
      match goal with
      | [|- (if ?a then true else false) = true] =>
        destruct a; intros
      end.
      trivial.
      exfalso.
      eapply n.
      (* seems to be off by one, but the error doesn't appear in the bounds *)
      assert (forall (A : Type)(ls : list A) a,
        In a (tl ls) -> In a ls).
      intros.
      destruct ls; simpl in *.
      intuition.
      intuition.
      eapply H26.
      eapply H23.
      
      match goal with
      | [H: (if ?a then true else false) = true |- _] =>
        case_eq a; intros
      end.
      eapply arrayLookup_Some_impl_In in H29.
      eapply in_map_iff; intuition.
      econstructor; intuition.
      eapply in_fst_split_if; eauto.
      rewrite H29 in H28.
      discriminate.

      fcf_simp.
      eapply comp_spec_ret; intuition.
      fcf_simp.
      eapply comp_spec_ret; intuition.
      fcf_simp.
      eapply comp_spec_ret; intuition.

    Qed.

    (* replace casKDF_rnd with compMap and rndList *)
    Definition CasKDF_IND_CPA_G6_bad_b1a_2 :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret false
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret false
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret false
          | Some lsR2 =>
            [_, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            cs2 <-$ rndOctetString digestLen;
            k2 <-$ rndOctetString secretLen;
            [k3, cs3] <-$2(
              k3 <-$ compMap _ (fun _ => rndOctetString secretLen) (forNats (length KE - S strongKE));
              cs3 <-$ rndList _ (rndOctetString digestLen) (length KE - S strongKE);
              ret (k3, cs3)
            );
            k <-$ rndOctetString secretLen;
            [_, s] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k3), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
            ) _ _ (nestedRandomFunc _ _ rndRange st1) nil;
            ret (any_dec (fun x => if (in_dec (EqDec_dec _) (snd (snd x)) (cs3++cs2::nil)) then true else false) (fst (split s)))
          end
        end
      end.

    Theorem casKDF_rnd_compMap_rndList_spec : 
      forall n, 
      comp_spec eq
      (casKDF_rnd n)
      (k3 <-$ compMap _ (fun _ => rndOctetString secretLen) (forNats n);
        cs3 <-$ rndList _ (rndOctetString digestLen) n;
        ret (k3, cs3)
      ).

      induction n; intuition; simpl in *.
      fcf_simp.
      eapply comp_spec_eq_refl.
    
      fcf_inline_first.
      fcf_swap leftc.
      fcf_skip.
      fcf_swap leftc.
      
      eapply eq_impl_comp_spec_eq.
      intros.
      eapply eqRat_trans.
      eapply evalDist_seq_eq_trans.
      intros.
      eapply comp_spec_eq_impl_eq.
      eapply IHn.
      fcf_inline_first; fcf_skip; fcf_simp.
      fcf_inline_first.
      fcf_at fcf_inline rightc 1%nat.
      fcf_swap rightc.
      fcf_skip.
      fcf_skip.
      fcf_simp.
      reflexivity.

    Qed.

    Theorem CasKDF_IND_CPA_G6_bad_b1a_2_equiv: 
      Pr[CasKDF_IND_CPA_G6_bad_b1a] == Pr[CasKDF_IND_CPA_G6_bad_b1a_2].

      unfold CasKDF_IND_CPA_G6_bad_b1a, CasKDF_IND_CPA_G6_bad_b1a_2.
      eapply comp_spec_eq_impl_eq.

      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      do 3 (fcf_inline_first; fcf_skip; fcf_simp).
      fcf_skip.
      eapply casKDF_rnd_compMap_rndList_spec.
      subst.
      eapply comp_spec_eq_refl.

      fcf_simp.
      eapply comp_spec_ret; intuition idtac.
      fcf_simp.
      eapply comp_spec_ret; intuition idtac.
      fcf_simp.
      eapply comp_spec_ret; intuition idtac.

    Qed.

    (* replace rndList with compMap *)
    Definition CasKDF_IND_CPA_G6_bad_b1a_3 :=
      [sk, P] <-$2 @keyGen _ _ _ _ _ _ (nth strongKE KE defKE);
      kR_opt <-$ (@responseFunc _ _ _ _ _ _ (nth strongKE KE defKE) P );
      lsSK1 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (firstn strongKE KE);    
      lsSK2 <-$ compMap _ (fun ke => @keyGen _ _ _ _ _ _ ke) (skipn (S strongKE) KE);
      lsR1_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (firstn strongKE KE) (snd (split lsSK1)));
      lsR2_opt <-$ compMap _ (fun p => @responseFunc _ _ _ _ _ _ (fst p) (snd p)) (combine (skipn (S strongKE) KE) (snd (split lsSK2)));
      match kR_opt with
      | None => ret false
      | Some (k_strong, R) =>
        match (stripOpt lsR1_opt) with
        | None => ret false
        | Some lsR1 =>
          match (stripOpt lsR2_opt) with
          | None => ret false
          | Some lsR2 =>
            [_, k1, st1] <-$3 (casKDF_cs psk
              (combine 
                (fst (split lsR1)) 
                (combine 
                  (combine (snd (split lsSK1)) (snd (split lsR1)))
                  (firstn strongKE context)
                )
              )) _ _ (rndHist _ _ rndRange) nil;
            k2 <-$ rndOctetString secretLen;
            cs3 <-$
              (cs2 <-$ rndOctetString digestLen;
              cs3 <-$ compMap _ (fun _ => rndOctetString digestLen) (forNats (length KE - S strongKE));
              ret (cs3 ++ cs2::nil)
            );
            k3 <-$ compMap _ (fun _ => rndOctetString secretLen) (forNats (length KE - S strongKE));
            k <-$ rndOctetString secretLen;
            [_, s] <-$2 (
              (A (snd (split lsSK1) ++ (P :: (snd (split lsSK2)))) (first (k1++k2::k3), (snd (split lsR1) ++ (R :: (snd (split lsR2))))) k)
            ) _ _ (nestedRandomFunc _ _ rndRange st1) nil;
            ret (any_dec (fun x => if (in_dec (EqDec_dec _) (snd (snd x)) cs3) then true else false) (fst (split s)))
          end
        end
      end.

    Theorem CasKDF_IND_CPA_G6_bad_b1a_3_equiv: 
      Pr[CasKDF_IND_CPA_G6_bad_b1a_2] == Pr[CasKDF_IND_CPA_G6_bad_b1a_3].

      unfold CasKDF_IND_CPA_G6_bad_b1a_2, CasKDF_IND_CPA_G6_bad_b1a_3.
      eapply comp_spec_impl_eq.

      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      fcf_inline_first; fcf_skip; fcf_simp.

      fcf_swap leftc.
      fcf_skip. 
      fcf_inline_first; fcf_skip; fcf_simp.
      fcf_swap rightc.
      fcf_inline_first; fcf_skip; fcf_simp.
      fcf_inline_first; fcf_skip.
      eapply rndList_map_perm.
      fcf_simp.
      
      fcf_inline_first; fcf_skip; fcf_simp.
      fcf_inline_first; fcf_skip; fcf_simp.
      eapply comp_spec_ret; intuition.

      apply any_dec_ex in H28.
      dest. intuition.
      match goal with
      | [H: (if ?a then _ else _) = true |- _] =>
          destruct a
      end.
      eapply ex_any_dec.
      eauto.
      match goal with
      | [|- (if ?a then _ else _) = true] =>
          destruct a
      end.
      trivial.
      exfalso.
      eapply n.
      eapply in_app_or in i.
      intuition.
      eapply in_or_app.
      left.
      eapply Permutation_in; eauto.
      discriminate.
      intuition.

      apply any_dec_ex in H28.
      dest. intuition.
      match goal with
      | [H: (if ?a then _ else _) = true |- _] =>
          destruct a
      end.
      eapply ex_any_dec.
      eauto.
      match goal with
      | [|- (if ?a then _ else _) = true] =>
          destruct a
      end.
      trivial.
      exfalso.
      eapply n.
      eapply in_app_or in i.
      intuition.
      eapply in_or_app.
      left.
      eapply Permutation_in.
      eapply Permutation_sym.
      eauto.
      trivial.
      discriminate.

      fcf_simp.
      eapply comp_spec_ret; intuition idtac.
      fcf_simp.
      eapply comp_spec_ret; intuition idtac.  
      eapply comp_spec_ret; intuition idtac.

    Qed.

    (* unroll the compMap at the tail to get to the next game *)
    Theorem CasKDF_IND_CPA_G6_bad_b1a_3_b2_equiv : 
      Pr[CasKDF_IND_CPA_G6_bad_b1a_3] == Pr[CasKDF_IND_CPA_G6_bad_b2].

      unfold CasKDF_IND_CPA_G6_bad_b1a_3, CasKDF_IND_CPA_G6_bad_b2.
      eapply comp_spec_eq_impl_eq.
      do 6 (fcf_skip; fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      do 2 (fcf_skip; fcf_simp).

      fcf_skip; fcf_simp.
      eapply comp_spec_eq_trans.
      2:{
      eapply comp_spec_eq_symm.
      eapply compMap_unroll_tl.
      rewrite forNats_length.
      assert (length KE - strongKE = S (length KE - S (strongKE))).
      lia.
      eauto.
      }
      fcf_swap leftc.
      fcf_skip.
      eapply compMap_spec.
      eapply list_pred_I.
      rewrite forNats_length.
      rewrite firstn_length.
      rewrite min_l.
      trivial.
      rewrite forNats_length.
      lia.
      intros.
      eapply comp_spec_eq_refl.
      fcf_skip.
      apply list_pred_eq_impl_eq in H19.
      subst.
      eapply comp_spec_eq_refl.

      subst.
      eapply comp_spec_eq_refl.

      fcf_simp.
      eapply comp_spec_ret; intuition idtac.
      fcf_simp.
      eapply comp_spec_ret; intuition idtac.
      eapply comp_spec_ret; intuition idtac.
      
      Unshelve.
      apply O.
    Qed.
      
    Theorem CasKDF_IND_CPA_G6_bad_b2_le : 
      Pr[CasKDF_IND_CPA_G6_bad_b1] <= Pr[CasKDF_IND_CPA_G6_bad_b2].

      rewrite CasKDF_IND_CPA_G6_bad_b1a_le.
      rewrite CasKDF_IND_CPA_G6_bad_b1a_2_equiv.
      rewrite CasKDF_IND_CPA_G6_bad_b1a_3_equiv.
      rewrite CasKDF_IND_CPA_G6_bad_b1a_3_b2_equiv.
      reflexivity.
    Qed.

    Theorem qam_state_length : forall (A B C: Set)(c : OracleComp A B C) q,
      queries_at_most c q ->
      forall (S1 : Set)(eqda : EqDec S1)(o : (list S1) -> A -> Comp (B * (list S1))) ls,
      (forall ls ls' a b, In (b, ls') (getSupport (o ls a)) -> length ls' <= S (length ls))%nat ->
      forall b x, 
      In (b, x) (getSupport (c _ _ o ls)) ->
      (length x <= q + (length ls))%nat.

      intuition.
      eapply le_trans. 
      eapply FCF.RndInList.qam_count_gen; eauto.
      intuition.
      rewrite Nat.add_1_l.
      eauto.
      rewrite mult_1_r.
      trivial.
    Qed.

    Theorem casKDF_wf : forall ls k eqd1 eqd2 o s ,
      (forall s a, well_formed_comp (o s a)) ->
      well_formed_comp
      ((casKDF k ls) eqd1 eqd2 o s).

      induction ls; intuition; simpl in *; wftac.
     
    Qed.

    Theorem casKDF_cs_wf : forall ls k eqd1 eqd2 o s ,
      (forall s a, well_formed_comp (o s a)) ->
      well_formed_comp
      ((casKDF_cs k ls) eqd1 eqd2 o s).

      induction ls; intuition; simpl in *; wftac.
      destruct p.
      simpl.
      wftac.
     
    Qed.

    Theorem CasKDF_IND_CPA_G6_bad_b2_small : 
      Pr[CasKDF_IND_CPA_G6_bad_b2] <= q * (length KE) / 2 ^ (digestLen * 8).

      unfold CasKDF_IND_CPA_G6_bad_b2.
      fcf_irr_l.
      eapply keyGen_wf.
      eapply nth_In.
      trivial.
      fcf_simp.
      fcf_irr_l.
      eapply responseFunc_wf.
      eapply nth_In.
      trivial.
      fcf_simp.
      fcf_irr_l.
      eapply compMap_wf.
      intuition.
      eapply keyGen_wf.
      eapply firstn_In.
      eauto.
      fcf_simp.
      fcf_irr_l.
      eapply compMap_wf.
      intuition.
      eapply keyGen_wf.
      destruct KE.
      trivial.
      simpl.
      right.
      eapply skipn_In.
      eauto.
      fcf_irr_l.
      eapply compMap_wf.
      intuition.
      eapply responseFunc_wf.
      destruct a; simpl in *.
      eapply firstn_In.
      eapply in_combine_l.
      eauto.
      fcf_simp.
      fcf_irr_l.
      eapply compMap_wf.
      intuition.
      eapply responseFunc_wf.
      destruct KE.
      simpl in *. trivial.
      simpl.
      right.
      destruct a; simpl in *.
      eapply skipn_In.
      eapply in_combine_l.
      eauto.
      fcf_simp.
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      fcf_irr_l.
      eapply casKDF_cs_wf.
      intuition.
      eapply rndHist_wf.
      wftac.
      fcf_simp.
      fcf_swap leftc.
      fcf_swap leftc.
      fcf_irr_l.
      eapply rndOctetString_wf.
      fcf_swap leftc.
      fcf_irr_l.
      eapply compMap_wf.
      intros.
      eapply rndOctetString_wf.
      fcf_swap leftc.
      fcf_irr_l.
      eapply rndOctetString_wf.
      fcf_swap leftc.
      fcf_irr_l.
      eapply oc_comp_wf.
      trivial.
      intuition.
      eapply nestedRandomFunc_wf.
      eapply rndRange_wf.
      assert (
        Pr [a <-$
    compMap (list_EqDec (Bvector_EqDec 8))
      (fun _ : nat => rndOctetString digestLen)
      (forNats (length KE - strongKE));
    [_, s]<-2 x7;
    ret any_dec
          (fun x8 : FullContext * (OctetString * list (Bvector 8)) =>
           if
            in_dec (EqDec_dec (list_EqDec (Bvector_EqDec 8)))
              (snd (snd x8)) a
           then true
           else false) (fst (split s)) ]
          ==
        Pr[RndListPred_G _ (rndOctetString digestLen)
          (fun
                 x5 =>
               if
                in_dec
                  (EqDec_dec _)
                  x5 (map (fun y => snd (snd y)) (fst (split (snd x7))))
               then true
               else false) (forNats (length KE - strongKE))]
      ).
      unfold RndListPred_G.
      fcf_skip.
      fcf_simp.
      eapply evalDist_ret_eq.
      simpl in *.
      rewrite any_dec_in_dec_swap.
      rewrite <- any_dec_map.
      eapply any_dec_f_eq.
      intuition.
 
      rewrite H13.
      rewrite RndListPred_Prob.
      assert (
        Pr [x8 <-$ rndOctetString digestLen;
    ret (if
          in_dec (EqDec_dec (list_EqDec (Bvector_EqDec 8))) x8
            (map
               (fun y : FullContext * (OctetString * OctetString) =>
                snd (snd y)) (fst (split (snd x7))))
         then true
         else false) ]
        ==
        Pr [(RndInList_G _ (rndOctetString digestLen)
          (map
                 (fun
                    y : FullContext *
                        (OctetString *
                         OctetString) =>
                  snd (snd y))
                 (fst (split (snd x7)))))]
      ).
      reflexivity.
      rewrite H14.
      rewrite (RndInList_Prob).
      rewrite forNats_length.
      rewrite map_length.
      rewrite (ratMult_comm _ (1/ 2 ^ (digestLen * 8))).
      rewrite <- ratMult_denom.
      rewrite ratMult_comm.
      rewrite <- ratMult_num_den.
      eapply leRat_terms.
      eapply mult_le_compat.
      rewrite split_length_l.
      destruct x7; simpl in *.
      erewrite qam_state_length; eauto.
      simpl.
      lia.
      intuition.
      unfold nestedRandomFunc in *.
      match goal with
      | [H: context[match ?a with | Some _ => _ | None => _ end ] |- _ ] =>
        case_eq a; intros
      end;
      rewrite H16 in H15.
      repeat simp_in_support.
      simpl.
      lia.
      unfold randomFunc in *.
      match goal with
      | [H: context[match ?a with | Some _ => _ | None => _ end ] |- _ ] =>
        case_eq a; intros
      end;
      rewrite H17 in H15;
      repeat simp_in_support;
      simpl;
      lia.
      lia.

      repeat rewrite posnatMult_eq.
      simpl.
      lia.

      eapply rndOctetString_wf.

      intuition.
      rewrite rndOctetString_uniform_le.
      rewrite expRat_terms.
      rewrite expnat_1.
      eapply leRat_terms.
      reflexivity.
      rewrite mult_comm.
      reflexivity.
     
      fcf_simp. 
      fcf_compute.
      eapply rat0_le_all.
      fcf_simp. 
      fcf_compute.
      eapply rat0_le_all. 
      fcf_compute.
      eapply rat0_le_all.
    Qed.

    Theorem CasKDF_IND_CPA_G6_bad1_small : 
      Pr[CasKDF_IND_CPA_G6_bad1] <= 
      (@KeyExchangeOW_CPA_List_Advantage _ _ _ _ _ _ _ (nth strongKE KE defKE) (fun q p => eqb q (fst (snd p))) strongKE_A)
      + (q * (length KE) / 2 ^ (digestLen * 8)).    

      rewrite CasKDF_IND_CPA_G6_bad2_le.
      rewrite CasKDF_IND_CPA_G6_bad2_split.
      rewrite CasKDF_IND_CPA_G6_bad_a2_equiv.
      rewrite CasKDF_IND_CPA_G6_bad_a2_OW_CPA_equiv.
      rewrite CasKDF_IND_CPA_G6_bad_b2_le.
      rewrite CasKDF_IND_CPA_G6_bad_b2_small.
      reflexivity.

    Qed.

    Theorem CasKDF_IND_CPA_G6_close : 
      | Pr[CasKDF_IND_CPA_G5 A] - Pr[CasKDF_IND_CPA_G6] | <=
      (@KeyExchangeOW_CPA_List_Advantage _ _ _ _ _ _ _ (nth strongKE KE defKE) (fun q p => eqb q (fst (snd p))) strongKE_A)
      + (q * (length KE) / 2 ^ (digestLen * 8)). 

      rewrite CasKDF_IND_CPA_G6_close_bad.
      eapply CasKDF_IND_CPA_G6_bad1_small.
    Qed.

    Theorem CasKDF_IND_CPA_G6_G5_equiv : 
      Pr[CasKDF_IND_CPA_G6] == Pr[CasKDF_IND_CPA_G5 (fun x y _ => z <--$$ rndOctetString secretLen; A x y z)].
      unfold CasKDF_IND_CPA_G6, CasKDF_IND_CPA_G5.
      do 6 (fcf_inline_first; fcf_skip; fcf_simp).
      destOpt.
      destOpt.
      destOpt.
      fcf_simp.
      do 5 (fcf_inline_first; fcf_skip; fcf_simp).
      reflexivity.

      fcf_simp.
      reflexivity.
      fcf_simp.
      reflexivity.
      reflexivity.
    Qed.

    Theorem CasKDF_G1_IND_CPA_G1_equiv : 
      Pr[CasKDF_IND_CPA_G1 (fun x y _ => z <--$$ rndOctetString secretLen; A x y z)]
      == Pr [ExpROM _ _ rndRange _ (KeyExchangeCPA_ROM_G1 (rndOctetString secretLen) A) ].

      Local Opaque evalDist.

      unfold ExpROM, KeyExchangeCPA_ROM_G1, CasKDF_IND_CPA_G1.
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

      simpl.
      fcf_inline_first.
      fcf_simp.
      simpl.
      fcf_inline_first.
      fcf_simp.
      reflexivity.

      Local Transparent evalDist.

    Qed.

    Theorem CasKDF_IND_CPA_ROM_Secure : 
      KeyExchangeCPA_O_Advantage (rndOctetString secretLen) A _ _ rndRange <=
      2/1 * (length KE * length KE / 2 ^ (8 * digestLen)) +
      (@KeyExchangeOW_CPA_List_Advantage _ _ _ _ _ _ _ (nth strongKE KE defKE) (fun q p => eqb q (fst (snd p))) strongKE_A)
      + (q * (length KE) / 2 ^ (digestLen * 8)).

      unfold KeyExchangeCPA_O_Advantage.
      rewrite CasKDF_IND_CPA_G1_equiv.
      rewrite <- CasKDF_G1_IND_CPA_G1_equiv.
      eapply leRat_trans.
      eapply ratDistance_le_trans.
      eapply CasKDF_G1_G5_close; intuition.
      rewrite ratDistance_comm.
      eapply ratDistance_le_trans.
      eapply CasKDF_G1_G5_close; intuition.
      econstructor.
      econstructor.
      eapply rndOctetString_wf.
      intuition.

      rewrite <- CasKDF_IND_CPA_G6_G5_equiv.
      rewrite ratDistance_comm.
      eapply CasKDF_IND_CPA_G6_close.
      rewrite ratAdd_assoc.
      rewrite <- ratAdd_assoc.
      eapply ratAdd_leRat_compat.
      eapply eqRat_impl_leRat.
      rewrite ratMult_2.
      eapply ratMult_comm.
      reflexivity.

    Qed.
  End CasKDF_IND_CPA_ROM.

End CasKDF_ROM.