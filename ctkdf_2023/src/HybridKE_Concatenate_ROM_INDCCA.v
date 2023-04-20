(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: MIT-0 *)

Set Implicit Arguments.

Require Import FCF.
Require Import FCF.CompFold.
Require Import FCF.OracleCompFold.
Require Import FCF.PRF.
Require Import FCF.ROM.
Require Import Permutation.

Require Import KeyExchange.
Require Import HybridKE_Concatenate.

Local Open Scope list_scope.


Ltac eqbTac_1 :=
  match goal with
  | [H : ?a ?= ?a = false |- _ ] =>
    rewrite eqb_refl in H; discriminate
   | [H : eqbPair _ _ ?a ?a = false |- _ ] =>
    rewrite eqbPair_refl in H; discriminate
  | [H : eqbPair _ _ _ _ = true |- _ ] =>
    apply eqbPair_prop in H; subst; try pairInv
   | [H : _ ?= _ = true |- _ ] =>
    rewrite eqb_leibniz in H; subst
  end.

Ltac eqbTac := repeat eqbTac_1; intuition idtac.

Ltac splitQuery :=
  match goal with
  | [|- context[match ?a with | cca_oq_ro d => _ | cca_oq_dec resp => _ end]] =>
    case_eq a; intros; subst
  end.

Theorem lengthsCorrect_flatten_eq_inv : forall x ls1 ls2,
  lengthsCorrect ls1 x = true ->
  lengthsCorrect ls2 x = true ->
  flatten ls1 = flatten ls2 ->
  ls1 = ls2.

  induction x; destruct ls1; destruct ls2; simpl in *; intuition idtac; try discriminate.
  apply andb_prop in H.
  apply andb_prop in H0.
  intuition idtac.
  eqbTac.
  apply app_eq_inv in H1;
  intuition idtac; subst.
  f_equal.
  eauto.
Qed.


Section CtKDF_ROM_CCA.
  
  Variable Salt OKM Info : Set.
  Hypothesis OKM_EqDec : EqDec OKM.
  Hypothesis Info_EqDec : EqDec Info.
  Hypothesis Salt_EqDec : EqDec Salt.
  Variable rndOKM : Comp OKM.
  Hypothesis rndOKM_wf : well_formed_comp rndOKM.

  Variable PrivateKey : Set.
  Variable PublicInit : Set.
  Variable PublicResponse : Set.
  Variable Aux AuxInfo : Set.

  Hypothesis PrivateKey_EqDec : EqDec PrivateKey.
  Hypothesis PublicInit_EqDec : EqDec PublicInit.
  Hypothesis PublicResponse_EqDec : EqDec PublicResponse.
  Hypothesis Aux_EqDec : EqDec Aux.
  Hypothesis AuxInfo_EqDec : EqDec AuxInfo.

  Variable projectInfo : (list PublicInit * list PublicResponse * AuxInfo) -> Info.
  Hypothesis projectInfo_injective : forall x y, projectInfo x = projectInfo y -> (x = y).
  Variable label : Salt.
  
  Definition BitStringKE := (@BitStringKE PrivateKey PublicInit PublicResponse Aux _ ).

  (* Assume we have a strong KE *)
  Variable strongKE : BitStringKE.
  Variable strongSecretLength : nat.

  Variable strongKE_Pos numAdditionalKEs : nat.
  Variable additionalSecretLengths : list nat.
  Hypothesis strongKE_Pos_small : 
      (strongKE_Pos <= (length additionalSecretLengths))%nat.


  Section CtKDF_IND_CCA_ROM.

    Definition KDF_OracleInput := (@KDF_OracleInput Salt Info).

    (* There is an adversary procedure that sees the public outpus of the strong KE and produces the other KE outputs. 
    This adversary procedure models a number of KEs that are under the control of the adversary. .*)
    Variable A_State : Set.
    Hypothesis A_State_EqDec : EqDec A_State.
    Variable A_KE : PublicInit -> PublicResponse -> OracleComp KDF_OracleInput OKM ((list (PublicInit * PublicResponse * BitString) * AuxInfo) * A_State).
    Hypothesis A_KE_wf : forall x y, well_formed_oc (A_KE x y).

    Definition ctKeyGen := (@ctKeyGen _ _ _ _ _ strongKE).

    Definition CtPublicResponse := (@CtPublicResponse PublicInit PublicResponse AuxInfo).

    Instance CtPublicResponse_EqDec : EqDec CtPublicResponse.

      unfold CtPublicResponse,
      HybridKE_Concatenate.CtPublicResponse.
      apply pair_EqDec;
      eauto with typeclass_instances.
      apply pair_EqDec;
      eauto with typeclass_instances.
    Qed.

    Definition ctResponseFunc p : OracleComp KDF_OracleInput OKM (option (OKM * CtPublicResponse * (Aux * A_State))) := 
      ((@ctResponseFunc Salt OKM Info _ PrivateKey PublicInit PublicResponse _ _ _ _ _ _ projectInfo label strongKE strongKE_Pos additionalSecretLengths A_State _ A_KE) p).

     Definition ctDecapsFunc  k r : OracleComp KDF_OracleInput OKM (option OKM) :=
      ((@ctDecapsFunc Salt OKM Info _ PrivateKey PublicInit PublicResponse _ _ _ projectInfo label strongKE strongKE_Pos additionalSecretLengths) k r).

    Instance CtKE : (@KeyExchange_ROM PrivateKey PublicInit CtPublicResponse OKM (Aux * A_State)  KDF_OracleInput OKM _ _ ) := {
      keyGen_ROM := $ctKeyGen;
      responseFunc_ROM := ctResponseFunc;
      decapsFunc_ROM := ctDecapsFunc
    }.

    Hypothesis strongDecaps_wf : forall x z,
      well_formed_comp (@decapsFunc _ _ _ _ _ _ _ strongKE x z).

    Hypothesis strongDecaps_deterministic : 
      forall a c d1 d2,
        In d1 (getSupport (@decapsFunc _ _ _ _ _ _ _ strongKE a c)) ->
        In d2 (getSupport (@decapsFunc _ _ _ _ _ _ _ strongKE a c)) ->
        d1 = d2.

    Hypothesis strongResponse_length_correct : forall x s r a,
      In (Some (s, r, a)) (getSupport (@responseFunc _ _ _ _ _ _ _ strongKE x)) ->
      length s = strongSecretLength.

    Hypothesis strongDecaps_length_correct : forall x z s,
      In (Some s) (getSupport (@decapsFunc _ _ _ _ _ _ _ strongKE x z)) ->
      length s = strongSecretLength.

    (* The strong KE is correct*)
    Definition strongKE_correctnessError := (@KE_CorrectnessError _ _ _ _ _ _ _ strongKE).

    Definition DomainRO := KDF_OracleInput.
    Definition RangeRO := OKM.

    Definition CCA_OracleQuery := (@CCA_OracleQuery CtPublicResponse DomainRO).
    Definition CCA_OracleResponse := (@CCA_OracleResponse RangeRO RangeRO).

    Variable A : PublicInit -> CtPublicResponse -> OKM -> (Aux * A_State) -> OracleComp CCA_OracleQuery CCA_OracleResponse bool.
    Hypothesis A_wf : forall w x y z, well_formed_oc (A w x y z).

    Instance CCA_OracleResponse_EqDec : EqDec CCA_OracleResponse.

      apply CCA_OracleResponse_EqDec; eauto with typeclass_instances.

    Qed.

    Instance CCA_OracleQuery_EqDec : EqDec CCA_OracleQuery.

      apply CCA_OracleQuery_EqDec; eauto with typeclass_instances.

    Qed.

    Theorem CCA_OracleResponse_inhabited : CCA_OracleResponse.

      apply (cca_or_dec None).

    Qed.

    Hint Resolve CCA_OracleResponse_inhabited : inhabited.

    (* unfold definitions and simplify *)

    Definition ccaOracle_G1(K : PrivateKey)(R : CtPublicResponse)( _ : unit)(q : CCA_OracleQuery) :  OracleComp DomainRO RangeRO (CCA_OracleResponse  * unit) :=
    match q with
    | cca_oq_ro d => r <--$ OC_Query _ d; $ret (cca_or_ro r, tt)
    | cca_oq_dec resp => 
      if (resp ?= R) then ($ret (cca_or_dec None, tt)) else
      r <--$ (
      s_opt <--$$ (@decapsFunc _ _ _ _ _ _ _ strongKE K (snd (fst resp)));
      match s_opt with
      | None => $ret None
      | Some s => 
        match (splitKdfInputs additionalSecretLengths (fst (snd resp)) strongKE_Pos) with
        | None => $ret None
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  =>     
          k <--$ query (((flatten (s1 ++ s :: s2))), label, (projectInfo ((Ps1 ++ (fst (fst resp)) :: Ps2), (Rs1 ++ (snd (fst resp)) :: Rs2), (snd (snd resp)))));
          $ret (Some k)
        end
      end
      ); $ret (cca_or_dec r, tt)
    end.

    Definition CtKDF_IND_CCA_G1 :=
      [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
      r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
      match r_opt with
      | None => ret false
      | Some (s, R, a) =>
        p <-$ (A_KE P R) _ _ (randomFunc rndOKM _) nil;
        [ls, auxInfo, s_A] <-3 (fst p);
        st <- (snd p);
        match (splitKdfInputs additionalSecretLengths ls strongKE_Pos) with
        | None => ret false
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2) => 
          [k, st'] <-$2 randomFunc rndOKM _ st (((flatten (s1 ++ s :: s2))), label,  (projectInfo ((Ps1 ++ P :: Ps2), (Rs1 ++ R :: Rs2), auxInfo)));
          p <-$ ( [z, _] <--$2 OC_Run _ _ _ (A P ((P, R), (ls, auxInfo)) k (a, s_A)) (ccaOracle_G1 sk ((P, R), (ls, auxInfo))) tt; 
          $ret z) _ _ (randomFunc rndOKM _) st';
          ret (fst p)
        end
      end.

    Theorem CtKDF_IND_CCA_G1_equiv : 
      Pr [ExpROM _ _ rndOKM _ (KeyExchangeCCA_ROM_G0 _ _ A) ] ==
      Pr [CtKDF_IND_CCA_G1].

      unfold CtKDF_IND_CCA_G1, ExpROM, KeyExchangeCCA_ROM_G0.
      fcf_sp.
      unfold ctKeyGen, HybridKE_Concatenate.ctKeyGen.
      fcf_sp.
      splitOpt; fcf_sp.
      fcf_skip.
      simpl. fcf_sp.
      splitOpt; fcf_sp.
      fcf_skip.
      fcf_sp.
      fcf_skip.
      eapply (fcf_oracle_eq eq).
      reflexivity.
      intros; subst.
      unfold ccaOracle_G1, ccaOracle_ROM.
      unfold decapsFunc_ROM.
      simpl.
      splitQuery.
      fcf_sp.
      splitIf; fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      simpl; fcf_sp.
      destruct b5; simpl in *; subst; trivial.
      destruct b5; simpl in *; subst; trivial.

    Qed.

    (* Give an independent random value to the adversary. This is indistinguishable as long as the adversary does not query on the IKM value. *)
    Definition CtKDF_IND_CCA_G2 :=
      [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
      r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
      match r_opt with
      | None => ret false
      | Some (s, R, a) =>
        p <-$ (A_KE P R) _ _ (randomFunc rndOKM _) nil;
        [ls, auxInfo, s_A] <-3 (fst p);
        st <- (snd p);
        match (splitKdfInputs additionalSecretLengths ls strongKE_Pos) with
        | None => ret false
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2) => 
          k' <-$ rndOKM;
          [k, st'] <-$2 randomFunc rndOKM _ st (((flatten (s1 ++ s :: s2))), label,  (projectInfo ((Ps1 ++ P :: Ps2), (Rs1 ++ R :: Rs2), auxInfo)));
          p <-$ ( [z, _] <--$2 OC_Run _ _ _ (A P ((P, R), (ls, auxInfo)) k' (a, s_A)) (ccaOracle_G1 sk ((P, R), (ls, auxInfo))) tt; 
          $ret z) _ _ (randomFunc rndOKM _) st';
          ret (fst p)
        end
      end.

    (* Identical until bad argument. Use a CCA oracle that keeps track of the bad event *)
    (* The oracle never goes bad when handling decrypt queries, because the CCA check prevents the attacker from indirectly querying the RO on the value associated with ths challenge. *)
    Definition ccaOracle_G2(K : PrivateKey)(P : PublicInit)(R : CtPublicResponse)(strongIKM : DomainRO)( bad : bool)(q : CCA_OracleQuery) :  OracleComp DomainRO RangeRO (CCA_OracleResponse  * bool) :=
    match q with
    | cca_oq_ro d => 
      r <--$ OC_Query _ d; 
      $ret (cca_or_ro r, bad || (d ?= strongIKM))
    | cca_oq_dec resp => 
      if (resp ?= R) then ($ret (cca_or_dec None, bad)) else
      r <--$ (
      s_opt <--$$ (@decapsFunc _ _ _ _ _ _ _ strongKE K (snd (fst resp)));
      match s_opt with
      | None => $ret (None, bad)
      | Some s => 
        match (splitKdfInputs additionalSecretLengths (fst (snd resp)) strongKE_Pos) with
        | None => $ret (None, bad)
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  =>     
          q <- (((flatten (s1 ++ s :: s2))), label, (projectInfo ((Ps1 ++ (fst (fst resp)) :: Ps2), (Rs1 ++ (snd (fst resp)) :: Rs2), (snd (snd resp)))));
          k <--$ query q;
          $ret (Some k, bad)
        end
      end
      ); $ret (cca_or_dec (fst r), snd r)
    end.

    Definition CtKDF_IND_CCA_G1_0 :=
      [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
      r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
      match r_opt with
      | None => ret (false, false)
      | Some (s, R, a) =>
        p <-$ (A_KE P R) _ _ (randomFunc rndOKM _) nil;
        [ls, auxInfo, s_A] <-3 (fst p);
        st <- (snd p);
        match (splitKdfInputs additionalSecretLengths ls strongKE_Pos) with
        | None => ret (false, false)
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2) => 
          q <- (((flatten (s1 ++ s :: s2))), label,  (projectInfo ((Ps1 ++ P :: Ps2), (Rs1 ++ R :: Rs2), auxInfo)));
          bad <- if (arrayLookup _ st q) then true else false;
          [k, st'] <-$2 randomFunc rndOKM _ st q;
          p <-$ (OC_Run _ _ _ (A P ((P, R), (ls, auxInfo)) k (a, s_A)) (ccaOracle_G2 sk P ((P, R), (ls, auxInfo)) q) bad) _ _ (randomFunc rndOKM _) st';
          ret (fst p)
        end
      end.

    Definition CtKDF_IND_CCA_G1_1 :=
      [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
      r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
      match r_opt with
      | None => ret (false, false)
      | Some (s, R, a) =>
        p <-$ (A_KE P R) _ _ (randomFunc rndOKM _) nil;
        [ls, auxInfo, s_A] <-3 (fst p);
        st <- (snd p);
        match (splitKdfInputs additionalSecretLengths ls strongKE_Pos) with
        | None => ret (false, false)
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2) => 
          q <- (((flatten (s1 ++ s :: s2))), label,  (projectInfo ((Ps1 ++ P :: Ps2), (Rs1 ++ R :: Rs2), auxInfo)));
          bad <- if (arrayLookup _ st q) then true else false;
          k' <-$ rndOKM;
          [k, st'] <-$2 randomFunc rndOKM _ st q;
          p <-$ (OC_Run _ _ _ (A P ((P, R), (ls, auxInfo)) k' (a, s_A)) (ccaOracle_G2 sk P ((P, R), (ls, auxInfo)) q) bad) _ _ (randomFunc rndOKM _) st';
          ret (fst p)
        end
      end.

    Theorem CtKDF_IND_CCA_G1_0_equiv : 
      Pr[CtKDF_IND_CCA_G1] == Pr[x <-$ CtKDF_IND_CCA_G1_0; ret (fst x)].

      unfold CtKDF_IND_CCA_G1, CtKDF_IND_CCA_G1_0.
      fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      fcf_skip.
      eapply (fcf_oracle_eq (fun x y => snd x = snd y)); intuition idtac.
      simpl in *; subst.
      unfold ccaOracle_G1, ccaOracle_G2.
      splitQuery; fcf_sp.
      splitIf; fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      simpl; fcf_sp.
      symmetry; trivial.
      trivial.

    Qed.

    Theorem CtKDF_IND_CCA_G1_1_G2_equiv : 
      Pr[x <-$ CtKDF_IND_CCA_G1_1; ret (fst x)] == Pr[CtKDF_IND_CCA_G2].

      unfold CtKDF_IND_CCA_G1_1, CtKDF_IND_CCA_G2.
      fcf_sp.
      splitOpt; fcf_sp.     
      splitOpt; fcf_sp.
      fcf_skip.
      eapply (fcf_oracle_eq (fun x y => snd x = snd y)); intuition idtac.
      simpl in *; subst.
      unfold ccaOracle_G1, ccaOracle_G2.
      splitQuery; fcf_sp.
      splitIf; fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      simpl; fcf_sp.
      symmetry; trivial.
      trivial.
    Qed.

    Theorem ccaOracle_G1_wf : forall a b c d,  
      well_formed_oc (ccaOracle_G1 a b c d).

      intros.
      unfold ccaOracle_G1.
      wftac.
      destruct d; wftac.
      splitIf; wftac.
      intros.
      splitOpt; wftac.
      splitOpt; wftac.
      destruct p.
      destruct p.
      destruct p.
      destruct p.
      destruct p.
      wftac.

    Qed.

    Local Opaque getSupport.

    Ltac splitOr_r :=
      match goal with
      | [|- context [_ || ?a]] => case_eq a; intros; subst
      end.

    Ltac splitOpt2 :=
       match goal with
      | [ |- comp_spec _ (Bind (match ?a with | Some _ => _ | None => _ end) _ ) (Bind (match ?b with | Some _ => _ | None => _ end)  _ )] =>
        replace b with a; [case_eq a; intros | try reflexivity]
      end.


    Theorem lengthsCorrect_impl_length_correct : forall ls1 ls2,
      lengthsCorrect ls1 ls2 = true ->
      length ls1 = length ls2.

      induction ls1; destruct ls2; intros; simpl in *; trivial; try discriminate.     
      apply andb_prop in H.
      intuition idtac.
      eqbTac.
      f_equal; eauto.

    Qed.

    Theorem splitKdfInputs_eq_inv :  forall n lsa (lsb1 lsb2: list (PublicInit * PublicResponse * BitString)) x y,
      splitKdfInputs lsa lsb1 n = Some x -> 
      splitKdfInputs lsa lsb2 n = Some y ->
      x = y -> 
      lsb1 = lsb2.

      intros.
      unfold splitKdfInputs in *.
      unfold setLet in *.
      subst.

      repeat 
      match goal with
      | [H: Some _ = Some _ |- _ ] =>
        inversion H; clear H; subst; try pairInv
      | [H: (if (negb ?a) then _ else _) = _, H1 : ?a = _ |- _ ]=>
        rewrite H1 in H; simpl in *; try discriminate
      | [H: (if (negb ?a) then _ else _) = _ |- _ ]=>
        case_eq a; intros
      end.

      rewrite <- (combine_split_eq lsb1).
      rewrite <- (combine_split_eq lsb2).
      rewrite <- (combine_split_eq (fst (split lsb1))).
      rewrite <- (combine_split_eq (fst (split lsb2))).

      rewrite <- (firstn_skipn n lsb1).
      rewrite <- (firstn_skipn n lsb2).
      repeat rewrite fst_split_app.
      repeat rewrite snd_split_app.
      repeat (f_equal; trivial).

    Qed.

    Theorem splitKdfInputs_length_eq : forall n lsa (lsb1 lsb2: list (PublicInit * PublicResponse * BitString)) a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2,
      splitKdfInputs lsa lsb1 n = Some (a1, b1, c1, d1, e1, f1) ->
      splitKdfInputs lsa lsb2 n = Some (a2, b2, c2, d2, e2, f2) ->
      (length a1 = length a2) /\ (length b1 = length b2) /\ (length c1 = length c2) /\ (length d1 = length d2) /\ (length e1 = length e2) /\ (length f1 = length f2).

      intros.
      unfold splitKdfInputs in *.
      case_eq (lengthsCorrect (snd (split lsb1)) lsa); intros;
      rewrite H1 in H; simpl in *; try discriminate.
      case_eq (lengthsCorrect (snd (split lsb2)) lsa); intros;
      rewrite H2 in H0; simpl in *; try discriminate.
      unfold setLet in *.
      inversion H; clear H; subst.
      inversion H0; clear H0; subst.
      apply lengthsCorrect_impl_length_correct in H1.
      apply lengthsCorrect_impl_length_correct in H2.
      repeat rewrite split_length_l.
      repeat rewrite split_length_r in *.
      repeat rewrite split_length_l.
      repeat rewrite firstn_length.
      repeat rewrite skipn_length.
      rewrite <- H2 in H1.
      intuition idtac; f_equal; trivial.
      
    Qed.

    Theorem splitKdfInputs_length_eq_1 : forall n lsa (lsb1 lsb2: list (PublicInit * PublicResponse * BitString)) a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2,
      splitKdfInputs lsa lsb1 n = Some (a1, b1, c1, d1, e1, f1) ->
      splitKdfInputs lsa lsb2 n = Some (a2, b2, c2, d2, e2, f2) ->
      (length a1 = length a2).

      intros.
      specialize (@splitKdfInputs_length_eq n lsa lsb1 lsb2 a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2); intuition idtac.

    Qed.

    Theorem splitKdfInputs_length_eq_2 : forall n lsa (lsb1 lsb2: list (PublicInit * PublicResponse * BitString)) a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2,
      splitKdfInputs lsa lsb1 n = Some (a1, b1, c1, d1, e1, f1) ->
      splitKdfInputs lsa lsb2 n = Some (a2, b2, c2, d2, e2, f2) ->
      (length b1 = length b2).

      intros.
      specialize (@splitKdfInputs_length_eq n lsa lsb1 lsb2 a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2); intuition idtac.

    Qed.

    Theorem splitKdfInputs_length_eq_3 : forall n lsa (lsb1 lsb2: list (PublicInit * PublicResponse * BitString)) a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2,
      splitKdfInputs lsa lsb1 n = Some (a1, b1, c1, d1, e1, f1) ->
      splitKdfInputs lsa lsb2 n = Some (a2, b2, c2, d2, e2, f2) ->
      (length c1 = length c2).

      intros.
      specialize (@splitKdfInputs_length_eq n lsa lsb1 lsb2 a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2); intuition idtac.

    Qed.

      Theorem split_firstn_eq :  forall (A B : Type) n (ls : list (A * B)) lsa1 lsa2 lsb1 lsb2,
      (lsa1, lsb1) = (split ls) ->
      (lsa2, lsb2) = (split (firstn n ls)) ->
      (lsa2 = (firstn n lsa1) /\ lsb2 = (firstn n lsb1)).

      induction n; destruct ls; intros; simpl in *; repeat pairInv. 
      intuition idtac.
      intuition idtac.
      intuition idtac.
      destruct p.
      remember (split ls) as z. destruct z.
      remember (split (firstn n ls)) as z. destruct z.
      repeat pairInv.
      match goal with
      | [|- ?a :: ?lsa1 = ?a :: ?lsa2 /\ ?b :: ?lsb1 = ?b :: ?lsb2] =>
        assert (lsa1 = lsa2 /\ lsb1 = lsb2)
      end.
      eapply IHn; eauto.
      intuition idtac; subst; reflexivity.

    Qed.

    Theorem snd_split_firstn_eq : forall (X Y : Type) n (ls : list (X * Y)),
      snd (split (firstn n ls)) = firstn n (snd (split ls)).

      intros.
      remember (split ls) as z.
      destruct z.
      remember (split (firstn n ls)) as z.
      destruct z.
      specialize (@split_firstn_eq X Y n ls l l1 l0 l2); intuition idtac.
    Qed.

    Theorem fst_split_firstn_eq : forall (X Y : Type) n (ls : list (X * Y)),
      fst (split (firstn n ls)) = firstn n (fst (split ls)).

      intros.
      remember (split ls) as z.
      destruct z.
      remember (split (firstn n ls)) as z.
      destruct z.
      specialize (@split_firstn_eq X Y n ls l l1 l0 l2); intuition idtac.
    Qed.

    Theorem split_skipn_eq :  forall (A B : Type) n (ls : list (A * B)) lsa1 lsa2 lsb1 lsb2,
      (lsa1, lsb1) = (split ls) ->
      (lsa2, lsb2) = (split (skipn n ls)) ->
      (lsa2 = (skipn n lsa1) /\ lsb2 = (skipn n lsb1)).

      induction n; destruct ls; intros; simpl in *; repeat pairInv. 
      intuition idtac.
      destruct p.
      remember (split ls) as z. destruct z.
      repeat pairInv.
      intuition idtac.
      intuition idtac.
      destruct p.
      remember (split ls) as z. destruct z.
      repeat pairInv.
      eapply IHn; eauto.

    Qed.

    Theorem snd_split_skipn_eq : forall (X Y : Type) n (ls : list (X * Y)),
      snd (split (skipn n ls)) = skipn n (snd (split ls)).

      intros.
      remember (split ls) as z.
      destruct z.
      remember (split (skipn n ls)) as z.
      destruct z.
      specialize (@split_skipn_eq X Y n ls l l1 l0 l2); intuition idtac.
    Qed.

    Theorem fst_split_skipn_eq : forall (X Y : Type) n (ls : list (X * Y)),
      fst (split (skipn n ls)) = skipn n (fst (split ls)).

      intros.
      remember (split ls) as z.
      destruct z.
      remember (split (skipn n ls)) as z.
      destruct z.
      specialize (@split_skipn_eq X Y n ls l l1 l0 l2); intuition idtac.
    Qed.

    Theorem lengthsCorrect_split : forall n ls1 ls2 a b,
      (n <= length ls1)%nat ->
      (n <= length ls2)%nat ->
      lengthsCorrect (firstn n ls1 ++ (a :: (skipn n ls1))) (firstn n ls2 ++ (b :: (skipn n ls2))) = 
      ((length a ?= b) && (lengthsCorrect ls1 ls2)).

      induction n; intros; simpl in *; trivial.
      destruct ls1; destruct ls2; simpl in *; trivial; try lia.
      rewrite IHn; try lia.
      repeat rewrite andb_assoc.
      f_equal.
      apply andb_comm.

    Qed.

    Theorem any_dec_eq_arrayLookup : forall (A B : Set)(eqd : EqDec A)(ls : list (A * B)) a,
      any_dec (eqb a) (fst (split ls)) = if (arrayLookup _ ls a) then true else false.

      induction ls; intros.
      reflexivity.
      rewrite fst_split_cons.
      rewrite any_dec_cons.
      simpl.
      destruct a; simpl.
      case_eq (a0 ?= a); intros.
      eqbTac.
      simpl.
      eapply IHls.

    Qed.

    Theorem pair_any_dec_eq_arrayLookup : forall (A1 A2  B : Set)(eqd1 : EqDec A1)(eqd2 : EqDec A2)(ls : list ((A1 * A2) * B)) a,
      any_dec (eqbPair _ _ a) (fst (split ls)) = if (arrayLookup _ ls a) then true else false.

      intros.
      specialize (@any_dec_eq_arrayLookup (A1 * A2) B (pair_EqDec eqd1 eqd2) ls a); intros.
      simpl in *.
      eauto.

    Qed.

    Theorem any_dec_true_impl_arrayLookup_Some : forall (A B : Set)(eqd : EqDec A)(ls : list (A * B)) a,
      any_dec (eqb a) (fst (split ls)) = true ->
      exists b, arrayLookup _ ls a = Some b.

      intros. 
      rewrite any_dec_eq_arrayLookup in H.
      destruct (arrayLookup eqd ls a); try discriminate.
      econstructor; eauto.

    Qed.

    Theorem arrayLookup_Some_true_impl_any_dec_true : forall (A B : Set)(eqd : EqDec A)(ls : list (A * B)) a b,
      arrayLookup _ ls a = Some b ->
      any_dec (eqb a) (fst (split ls)) = true.

      intros. 
      rewrite any_dec_eq_arrayLookup.
      destruct (arrayLookup eqd ls a); try discriminate.
      trivial.

    Qed.

    Definition read ls len : (BitString * BitString) :=
      (firstn len ls, skipn len ls).

    Fixpoint readLengths ls lens : ((list BitString) * BitString) :=
      match lens with
        | nil => (nil, ls)
        | len :: lens' =>
          [s1, ls1] <-2 read ls len;
          [s2, ls2] <-2 readLengths ls1 lens';
          ((s1 :: s2),  ls2)
      end.

    Definition toSecrets ls : list (BitString) * BitString :=
      readLengths ls ((firstn strongKE_Pos additionalSecretLengths) ++ (strongSecretLength :: (skipn strongKE_Pos additionalSecretLengths))).

    Definition splitSecrets(ls : BitString) :  ((list BitString) * (option BitString) * (list BitString)) * BitString :=
      [lss, ls'] <-2 toSecrets ls;
      ls1 <- firstn strongKE_Pos lss;
      s <- nth strongKE_Pos lss nil;
      ls2 <- skipn (S strongKE_Pos) lss;
      ((ls1, Some s, ls2), ls').

    Theorem readLengths_eq_inv : forall lens ls1 ls2,
      readLengths ls1 lens = readLengths ls2 lens ->
      ls1 = ls2.

      induction lens; intros; simpl in *.
      pairInv.
      reflexivity.

      remember (readLengths (skipn a ls1) lens) as z1.
      remember (readLengths (skipn a ls2) lens) as z2.
      destruct z1.
      destruct z2.
      pairInv.
      rewrite <- (firstn_skipn a ls1).
      rewrite <- (firstn_skipn a ls2).
      f_equal.
      trivial.
      eapply IHlens.
      rewrite <- Heqz1.
      rewrite <- Heqz2.
      reflexivity.

    Qed.

    Theorem readLengths_length : forall lens ls,
      length (fst (readLengths ls lens)) = length lens.

      induction lens; intros; simpl in *.
      trivial.
      remember (readLengths (skipn a ls) lens) as z.
      destruct z.
      simpl.
      f_equal.
      erewrite <- IHlens.
      rewrite <- Heqz.
      reflexivity.

    Qed.

      Theorem toSecrets_eq_inv : forall ls1 ls2,
        toSecrets ls1 = toSecrets ls2 ->
        ls1 = ls2.

        intros.
        eapply readLengths_eq_inv.
        eauto.
   
      Qed.

      Theorem toSecrets_length_eq : forall ls1 ls2,
        length (fst (toSecrets ls1)) = length (fst (toSecrets ls2)).

        intros.
        unfold toSecrets.
        repeat rewrite readLengths_length.
        reflexivity.
      Qed.

      Theorem splitSecrets_eq_inv : forall ls1 ls2,
        splitSecrets ls1 = splitSecrets ls2 ->
        ls1 = ls2.

        intros.
        eapply toSecrets_eq_inv.
        unfold splitSecrets in *.
        unfold setLet in *.
        simpl in *.
        remember (toSecrets ls1) as z1.
        remember (toSecrets ls2) as z2.
        destruct z1.
        destruct z2.
        pairInv.
        f_equal.
        assert (length l = length l0).
        replace l with (fst (toSecrets ls1)).
        replace l0 with (fst (toSecrets ls2)).
        apply toSecrets_length_eq.
        rewrite <- Heqz2.
        reflexivity.
        rewrite <- Heqz1.
        reflexivity.

        destruct (le_dec (length l) strongKE_Pos).
        erewrite <- (firstn_all2 l).
        erewrite <- (firstn_all2 l0).
        eauto.
        lia.
        lia.

        rewrite (@lsAppCons _ l strongKE_Pos nil); try lia.
        rewrite (@lsAppCons _ l0 strongKE_Pos nil); try lia.
  
        f_equal.
        trivial.
        f_equal.
        trivial.
        simpl.
        trivial.
      Qed.

    Theorem firstn_app_eq_gen : forall (A : Type)(ls1 ls2 : list A) n,
      n = length ls1 ->
      firstn n (ls1 ++ ls2) = ls1.

      induction ls1; intros; subst; simpl in *; trivial.

      f_equal.
      eauto.

    Qed.

    Theorem skipn_app_eq_gen : forall (A : Type)(ls1 ls2 : list A) n,
      n = length ls1 ->
      skipn n (ls1 ++ ls2) = ls2.
    
      induction ls1; intros; subst; simpl in *; trivial.
      eauto.

    Qed.

    Definition secretLengthsCorrect (ls : list BitString) :=
      lengthsCorrect ls (firstn strongKE_Pos additionalSecretLengths ++ (strongSecretLength :: (skipn strongKE_Pos additionalSecretLengths))) = true.

    Theorem readLengths_inverse : forall ls lens,
      lengthsCorrect ls lens = true ->
      readLengths (flatten ls) lens = (ls, nil).

      induction ls; destruct lens; intros; simpl in *; trivial; try discriminate.
      remember (readLengths (skipn n (a ++ (flatten ls))) lens) as z.
      destruct z.
      apply andb_prop in H.
      intuition idtac.
      eqbTac; subst.
      rewrite firstn_app_eq.
      rewrite skipn_app_eq_gen in Heqz; trivial.
      rewrite IHls in Heqz.
      pairInv.
      reflexivity.
      trivial.
    Qed.

    Theorem Forall2_map_r : forall (A B C : Type) P (lsa : list A)(lsb : list B)(f : B -> C),
      Forall2 (fun a b => P a (f b)) lsa lsb ->
      Forall2 P lsa (map f lsb).

      induction 1; intros; simpl in *; trivial.
      econstructor.
      trivial.
      eauto.
    Qed.

      Theorem toSecrets_flatten_eq : forall ls,
        secretLengthsCorrect ls ->
        toSecrets (flatten ls) = (ls, nil).

        intros.
        unfold toSecrets.
        apply readLengths_inverse.
        eauto.

      Qed.

      Theorem stripOpt_length_eq : forall (A : Type)(ls1 : list (option A)) ls2,
        stripOpt ls1 = Some ls2 ->
        length ls2 = length ls1.

        induction ls1; destruct ls2; intros; simpl in *; trivial.
        inversion H.
        destruct a; simpl in *.
        destruct (stripOpt ls1); simpl in *.
        inversion H.
        discriminate.
        discriminate.

        destruct a; simpl in *.
        remember (stripOpt ls1) as z.
        destruct z; simpl in *.
        inversion H; clear H; subst.
        f_equal.
        eapply IHls1; eauto.
        discriminate.
        discriminate.

      Qed.

      Theorem Forall2_symm : forall (A B : Type)(P : A -> B -> Prop) lsa lsb,
        Forall2 (fun b a => P a b) lsb lsa ->
        Forall2 P lsa lsb.

        induction lsa; intros; simpl in *.
        inversion H.
        econstructor.

        inversion H; clear H; subst.
        econstructor.
        trivial.
        eauto.

      Qed.

      Theorem stripOpt_Some_forall2 : forall (A : Type)(ls1 : list (option A)) ls2,
        stripOpt ls1 = Some ls2 ->
        Forall2 (fun x y => x = Some y) ls1 ls2.

        induction ls1; intros; simpl in *.
        inversion H.
        econstructor.

        unfold maybeBind in *.
        destruct a.
        case_eq (stripOpt ls1); intros;
        rewrite H0 in H.
        inversion H; clear H; subst.
        econstructor.
        reflexivity.
        eauto.
        discriminate.
        discriminate.

      Qed.

      Theorem stripOpt_Some_map: forall (A : Type)(ls1 : list (option A)) ls2,
        stripOpt ls1 = Some ls2 ->
        map Some ls2 = ls1.

        induction ls1; intros; simpl in *.
        inversion H; subst; reflexivity.
     
        unfold maybeBind in *.
        destruct a.
        case_eq (stripOpt ls1); intros;
        rewrite H0 in H.
        inversion H; clear H; subst.
        simpl.
        f_equal.
        eauto.
     
        discriminate.
        discriminate.

      Qed.

      Theorem stripOpt_Some_map': forall (A : Type)(ls1 : list (option A)) ls2 def,
        stripOpt ls1 = Some ls2 ->
        ls2 = map (fun o => match o with | Some x => x | None => def end) ls1.

        induction ls1; intros; simpl in *.
        inversion H; subst; reflexivity.
     
        unfold maybeBind in *.
        destruct a.
        case_eq (stripOpt ls1); intros;
        rewrite H0 in H.
        inversion H; clear H; subst.
        f_equal.
        eauto.
     
        discriminate.
        discriminate.

      Qed.

      Theorem Forall2_map_l : forall (A B C : Type)(P : C -> B -> Prop) (f : A -> C) lsa lsb,
        Forall2 (fun a b=> P (f a) b) lsa lsb ->
        Forall2 P (map f lsa) lsb.

        induction lsa; intros; simpl in *.
        inversion H. econstructor.
        inversion H; clear H; subst.
        econstructor.
        trivial.
        eauto.

      Qed.

      Theorem compMap_support_Forall2 : 
  forall [A : Type][B : Set] (P : A -> B -> Prop) (eqd : EqDec B) (c : A -> Comp B) (lsa : list A) (lsb : list B),
  In lsb (getSupport (compMap eqd c lsa)) -> (forall (a : A) (b : B), In a lsa -> In b (getSupport (c a)) -> P a b) -> Forall2 P lsa lsb.

        induction lsa; intros; simpl in *.
        simp_in_support.
        econstructor.
        repeat simp_in_support.
        econstructor.
        eapply H0; intuition idtac.
        eapply IHlsa; eauto.
      Qed.

      Theorem Forall2_impl':
        forall [A B : Type] [lsa : list A] [lsb : list B] [P1 : A -> B -> Prop] (P2 : A -> B -> Prop),
        Forall2 P1 lsa lsb -> (forall (a : A) (b : B), In a lsa -> In b lsb -> P1 a b -> P2 a b) -> Forall2 P2 lsa lsb.

        induction lsa; intros.
        inversion H. econstructor.
        inversion H; clear H; subst.
        econstructor.
        eapply H0; simpl; intuition idtac.
        eapply IHlsa; eauto.
        intros.
        eapply H0; simpl; intuition idtac.

      Qed.

      Theorem map_fst_eq': forall (A B : Type)(lsa : list A)(lsb : list B),
        length lsa = length lsb -> map fst (combine lsa lsb) = lsa.

        induction lsa; intros; simpl in *.
        destruct lsb; simpl in *; trivial; lia.
        destruct lsb; simpl in *; try lia.
        f_equal.
        eapply IHlsa.
        lia.

      Qed.

      Theorem firstn_impl_length_le : forall (A : Type)(ls1 ls2 : list A),
        firstn (length ls1) ls2 = ls1 ->
        (length ls1 <= length ls2)%nat.

        induction ls1; destruct ls2; intros; simpl in *; try lia.
        discriminate.
        assert (length ls1 <= length ls2)%nat.
        eapply IHls1.
        inversion H.
        rewrite H2.
        trivial.
        lia.

      Qed.

    Theorem nth_middle_gen: forall [A : Type] (l l' : list A) (a d : A) n, 
      n =  (length l) ->
      nth n (l ++ a :: l') d = a.
      
      intros.
      subst.
      apply nth_middle.

    Qed.

    Theorem skipn_app_cons_gen : forall (A : Type)(ls1 ls2 : list A)(a : A) n,
      n = length ls1 ->
      skipn (S n) (ls1 ++ (a :: ls2)) = ls2.

      intros. subst.
      replace (ls1 ++ (a :: ls2)) with ((ls1 ++ (a :: nil)) ++ ls2).
      apply skipn_app_eq_gen.
      rewrite app_length; simpl; lia.
      simpl.
      rewrite <- app_assoc.
      reflexivity.

    Qed.


      Ltac lengthTac_1 :=
    match goal with
      | [|- _ ?= _ = true] => 
        apply eqb_leibniz
      | [H: Some _ = Some _ |- _ ] =>
        inversion H; clear H; subst
      | [H: stripOpt _ = Some ?a |- context[length ?a]] =>
      apply stripOpt_length_eq in H; rewrite H
      | [H : In ?b (getSupport (compMap _ _ _)) |- context[length ?a]] =>
        apply compMap_length in H; rewrite H
      | [|- context [length (combine _ _)]] =>
        rewrite combine_length
      | [|- context [length (firstn _ _)]] =>
        rewrite firstn_length
      | [|- context[Init.Nat.min strongKE_Pos _]] =>
        rewrite (min_l strongKE_Pos)
      | [|- context[length (snd (split _))]] =>
        rewrite split_length_r
      | [|- context[length (fst (split _))]] =>
        rewrite split_length_l
      | [|- context[snd (split (firstn _ _))]] =>
        rewrite snd_split_firstn_eq
      | [|- context[snd (split (skipn _ _))]] =>
        rewrite snd_split_skipn_eq
      | [|- lengthsCorrect (firstn ?n ?ls1 ++ (?a :: (skipn ?n ?ls1))) (firstn ?n ?ls2 ++ (?b :: (skipn ?n ?ls2)))  = _] =>
        rewrite lengthsCorrect_split
      | [|- _ && _ = true] =>
        apply andb_true_intro; intuition idtac
      | [H1 : context[if ?a then _ else _], H2 : ?a = _ |- _ ] =>
        rewrite H2 in H1
      | [H : negb _ = false |- _ ] =>
        apply negb_false_iff in H
      | [H : lengthsCorrect ?ls1 ?ls2 = true |- _ ] =>
        apply lengthsCorrect_impl_length_correct in H
      | [H: length (snd (split _ )) = _ |- _] =>
        rewrite snd_split_length in H
      | [H: context[if ?a then _ else _]  |- _ ] =>
        case_eq a; intros
    end; trivial; try lia; try pairInv; try eqbTac.

Ltac lengthTac  := unfold splitKdfInputs in *; unfold setLet in *; unfold secretLengthsCorrect in *; 
  repeat lengthTac_1; try discriminate; eauto using strongDecaps_length_correct; 
  eauto using strongResponse_length_correct.


    Theorem splitKdfInputs_Some_lengthsCorrect : forall (X Y : Set) (x : list (X * Y * BitString)) l9 l10 l8 l7 l6 l5,
      splitKdfInputs additionalSecretLengths x strongKE_Pos = Some (l9, l10, l8, l7, l6, l5) ->
      lengthsCorrect (l8 ++ l5) additionalSecretLengths = true.

      intros.
      unfold splitKdfInputs in *.
      case_eq (lengthsCorrect (snd (split x)) additionalSecretLengths); intros;
      rewrite H0 in H;
      simpl in *.
      unfold setLet in *.
      inversion H; clear H; subst.
      rewrite snd_split_firstn_eq.
      rewrite snd_split_skipn_eq.
      rewrite firstn_skipn.
      trivial.
      discriminate.

    Qed.

    Theorem splitKdfInputs_Some_app_lengthsCorrect : forall (X Y : Set) (x : list (X * Y * BitString)) l9 l10 l8 l7 l6 l5 z,
      splitKdfInputs additionalSecretLengths x strongKE_Pos = Some (l9, l10, l8, l7, l6, l5) ->
      length z = strongSecretLength  ->
      lengthsCorrect (l8 ++ (z :: l5)) (((firstn strongKE_Pos additionalSecretLengths)) ++ (strongSecretLength :: (skipn strongKE_Pos  additionalSecretLengths))) = true.

      intros.
      replace l5 with (skipn strongKE_Pos (l8 ++ l5)).
      replace l8 with (firstn strongKE_Pos (l8 ++ l5)) at 1.
      rewrite lengthsCorrect_split.
      apply andb_true_intro.
      intuition idtac.
      apply eqb_leibniz.
      trivial.
      eapply splitKdfInputs_Some_lengthsCorrect; eauto.

      unfold splitKdfInputs in *.
      case_eq (lengthsCorrect (snd (split x)) additionalSecretLengths); intros;
      rewrite H1 in H; simpl in *;
      unfold setLet in *; simpl in *; try discriminate.
      inversion H; clear H; subst.
      rewrite snd_split_firstn_eq.
      rewrite snd_split_skipn_eq.
      rewrite firstn_skipn.
      apply lengthsCorrect_impl_length_correct in H1.
      lia.
      lia.
      unfold splitKdfInputs in *.
      case_eq ((lengthsCorrect (snd (split x)) additionalSecretLengths)); intros;
      rewrite H1 in H; unfold setLet in *; simpl in *; try discriminate.
      inversion H; clear H; subst.
      rewrite snd_split_firstn_eq.
      rewrite firstn_app_eq_gen.
      reflexivity.
      rewrite firstn_length.
      rewrite min_l. reflexivity.
      apply lengthsCorrect_impl_length_correct in H1.
      lia.
      unfold splitKdfInputs in *.
      case_eq ((lengthsCorrect (snd (split x)) additionalSecretLengths)); intros;
      rewrite H1 in H; unfold setLet in *; simpl in *; try discriminate.
      inversion H; clear H; subst.
      rewrite snd_split_firstn_eq.
      rewrite skipn_app_eq_gen.
      reflexivity.
      rewrite firstn_length.
      rewrite min_l. reflexivity.
      apply lengthsCorrect_impl_length_correct in H1.
      lia.

    Qed.


    Theorem ccaOracle_G2_preserves_bad : forall (S : Set)(eqdS : EqDec S) x a b c d (e : bool)(f : CCA_OracleQuery)(g : S -> DomainRO -> Comp (RangeRO * S)) s,
      e = true ->
      In x (getSupport (ccaOracle_G2 a b c d e f _ _ g s)) ->
      snd (fst x) = true.

      intros.
      unfold ccaOracle_G2 in *.
      destruct f; simpl in *; repeat simp_in_support.
      destruct x0; simpl in *; repeat simp_in_support.
      simpl.
      reflexivity.
      
      destruct  (c0 ?= c); simpl in *; repeat simp_in_support.
      reflexivity.
      destruct x2; simpl in *; repeat simp_in_support.
      destruct (splitKdfInputs additionalSecretLengths (fst (snd c0)) strongKE_Pos); simpl in *; repeat simp_in_support.
      destruct p. destruct p. destruct p. destruct p. destruct p.
      simpl in *; repeat simp_in_support.
      destruct x1; repeat simp_in_support.
      reflexivity.
      reflexivity.
      reflexivity.

    Qed.

    Theorem ccaOracle_G2_wf : forall a b c d e f,
      well_formed_oc (ccaOracle_G2 a b c d e f).

      intros.
      unfold ccaOracle_G2.
      destruct f; wftac.
      splitIf; wftac.
      intros.
      splitOpt; wftac.
      splitOpt; wftac.
      destruct p. destruct p. destruct p. destruct p. destruct p.
      wftac.

    Qed.
    
    Theorem CtKDF_IND_CCA_G1_0_1_eq_until_bad : forall x,
      evalDist CtKDF_IND_CCA_G1_0 (x, false) == evalDist CtKDF_IND_CCA_G1_1 (x, false).

      intros.
      unfold CtKDF_IND_CCA_G1_0, CtKDF_IND_CCA_G1_1.
      fcf_sp.
      splitOpt; fcf_sp.
      splitOpt.
      fcf_simp.
      unfold randomFunc.
      splitOpt.
      (* goes bad *)
      fcf_sp.
      fcf_irr_l.
      repeat (try apply pair_EqDec; try apply list_EqDec; eauto with typeclass_instances).
      eapply oc_comp_wf; eauto.
      intros. wftac.
      eapply oc_comp_wf.
      apply ccaOracle_G2_wf.
      intros.
      eapply randomFunc_wf; eauto.
      fcf_irr_r.
      fcf_sp.
      fcf_irr_r.
      repeat (try apply pair_EqDec; try apply list_EqDec; eauto with typeclass_instances).
      eapply oc_comp_wf; eauto.
      intros. wftac.
      eapply oc_comp_wf.
      apply ccaOracle_G2_wf.
      intros.
      eapply randomFunc_wf; eauto.
      fcf_sp.
      pairInv.
      destruct a1.
      eapply (oc_comp_invariant _ (fun x => (fst x) = true)) in H7.
      simpl in *.
      congruence.
      intros.
      repeat simp_in_support.
      simpl.
      eapply ccaOracle_G2_preserves_bad; eauto.
      simpl in *. trivial.
      pairInv.
      destruct b5.
      eapply (oc_comp_invariant _ (fun x => (fst x) = true)) in H9.
      simpl in *.
      congruence.
      intros.
      repeat simp_in_support.
      simpl.
      eapply ccaOracle_G2_preserves_bad; eauto.
      simpl in *. trivial.

      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_irr_r.
      fcf_sp.
      fcf_skip.
      match goal with
      | [|- context [ccaOracle_G2 _ _ _ ?a]] =>
       eapply (fcf_oracle_eq_until_bad (fun s => fst s) (fun s => fst s) (fun s1 s2 => forall x, x <>  a -> (arrayLookup _ (snd s1) x) = (arrayLookup _ (snd s2) x)))
      end.
      eauto.
      intros.
      wftac.
      eapply oc_comp_wf.
      apply ccaOracle_G2_wf.
      intros.
      eapply randomFunc_wf; eauto.
      intros.
      wftac.
      eapply oc_comp_wf.
      apply ccaOracle_G2_wf.
      intros.
      eapply randomFunc_wf; eauto.

      intros.
      match goal with 
      | [H : fst ?a = fst ?b |- _] =>
        destruct a; destruct b; simpl in *; subst
      end.
      unfold ccaOracle_G2.
      splitQuery; fcf_sp.
      splitOr_r; eqbTac.
      fcf_irr_l.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      eapply randomFunc_wf; eauto.
      fcf_irr_r.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      eapply randomFunc_wf; eauto.
      fcf_sp.
      rewrite orb_true_r in *.
      simpl in *; discriminate.
      rewrite orb_true_r in *.
      simpl in *; discriminate.

      unfold randomFunc.
      splitOpt2;
      fcf_sp.
      splitIf; eqbTac.
      eauto.
      eapply H10; intuition idtac; subst; eqbTac.
      
      splitIf; fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      
      match goal with
      | [H : forall y, (y = ?a -> False) -> _ |- context[arrayLookup _ _ ?x]] =>
        case_eq (eqb x a); intros
      end; eqbTac.
      pairInv.
      match goal with
      | [H : (?a ?= ?b) = false |- _ ] =>
        replace a with b in *; eqbTac
      end.
      apply projectInfo_injective in H18.
      pairInv.
      destruct c; simpl in *; f_equal.
      destruct p0; simpl in *; f_equal.
      apply app_eq_inv in H16.
      intuition idtac; subst.
      inversion H18; subst; trivial.
      eapply splitKdfInputs_length_eq_1; eauto.
      apply app_eq_inv in H19.
      intuition idtac; subst.
      inversion H18; subst; trivial.
      eapply splitKdfInputs_length_eq_2; eauto.
      destruct p1; simpl in *; f_equal.
      eapply splitKdfInputs_eq_inv; eauto.
      apply app_eq_inv in H16; intuition idtac.
      subst.
      apply app_eq_inv in H19; intuition idtac.
      subst.
      inversion H18; clear H18; subst.
      inversion H16; clear H16; subst.
      eapply lengthsCorrect_flatten_eq_inv in H17.
      apply app_eq_inv in H17; intuition idtac.
      inversion H16; clear H16; subst.
      reflexivity.
      eapply splitKdfInputs_length_eq_3; eauto.
      eapply splitKdfInputs_Some_app_lengthsCorrect; eauto.
      eapply splitKdfInputs_Some_app_lengthsCorrect; eauto.
      eapply splitKdfInputs_length_eq_2; eauto.
      eapply splitKdfInputs_length_eq_1; eauto.

      unfold randomFunc.
      splitOpt2; fcf_sp.
      splitIf; eqbTac.
      eauto.
      eapply H10; intuition idtac.
      rewrite H17 in H16. eqbTac.
      intros.
      simp_in_support.
      eapply ccaOracle_G2_preserves_bad in H12; eauto.
      simp_in_support.
      simpl. trivial.
      intros.
      simp_in_support.
      eapply ccaOracle_G2_preserves_bad in H12; eauto.
      simp_in_support.
      trivial.     
      
      intuition idtac.
      simpl.
      splitIf; eqbTac.
      reflexivity.
      
      simpl in *; fcf_sp.
      pairInv; intuition idtac.
      subst.
      reflexivity.
      pairInv; intuition idtac.
      subst. 
      reflexivity.

      fcf_sp.
    Qed.

    Theorem CtKDF_IND_CCA_G1_0_1_bad_eq : 
      Pr[ x <-$ CtKDF_IND_CCA_G1_0; ret (snd x)] == Pr[x <-$ CtKDF_IND_CCA_G1_1; ret (snd x)].

      intros.
      unfold CtKDF_IND_CCA_G1_0, CtKDF_IND_CCA_G1_1.
      fcf_sp.
      splitOpt; fcf_sp.
      splitOpt.
      
      fcf_simp.
      unfold randomFunc.
      splitOpt.
      (* goes bad *)
      fcf_sp.
      fcf_irr_l.
      repeat (try apply pair_EqDec; try apply list_EqDec; eauto with typeclass_instances).
      eapply oc_comp_wf; eauto.
      intros. wftac.
      eapply oc_comp_wf.
      apply ccaOracle_G2_wf.
      intros.
      eapply randomFunc_wf; eauto.
      fcf_irr_r.
      fcf_sp.
      fcf_irr_r.
      repeat (try apply pair_EqDec; try apply list_EqDec; eauto with typeclass_instances).
      eapply oc_comp_wf; eauto.
      intros. wftac.
      eapply oc_comp_wf.
      apply ccaOracle_G2_wf.
      intros.
      eapply randomFunc_wf; eauto.
      fcf_sp.
      destruct b5.
      eapply (oc_comp_invariant _ (fun x => (fst x) = true)) in H9.
      simpl in *.
      congruence.
      intros.
      repeat simp_in_support.
      simpl.
      eapply ccaOracle_G2_preserves_bad; eauto.
      simpl in *. trivial.
      destruct a1.
      eapply (oc_comp_invariant _ (fun x => (fst x) = true)) in H7.
      simpl in *.
      congruence.
      intros.
      repeat simp_in_support.
      simpl.
      eapply ccaOracle_G2_preserves_bad; eauto.
      simpl in *. trivial.

      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_irr_r.
      fcf_sp.
      fcf_skip.
      match goal with
      | [|- context [ccaOracle_G2 _ _ _ ?a]] =>
       eapply (fcf_oracle_eq_until_bad (fun s => fst s) (fun s => fst s) (fun s1 s2 => forall x, x <>  a -> (arrayLookup _ (snd s1) x) = (arrayLookup _ (snd s2) x)))
      end.
      eauto.
      (* wf *)
      intros.
      wftac.
      eapply oc_comp_wf.
      apply ccaOracle_G2_wf.
      intros.
      eapply randomFunc_wf; eauto.
      intros.
      wftac.
      eapply oc_comp_wf.
      apply ccaOracle_G2_wf.
      intros.
      eapply randomFunc_wf; eauto.

      intros.
      match goal with 
      | [H : fst ?a = fst ?b |- _] =>
        destruct a; destruct b; simpl in *; subst
      end.
      unfold ccaOracle_G2.
      splitQuery; fcf_sp.
      splitOr_r; eqbTac.
      fcf_irr_l.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      eapply randomFunc_wf; eauto.
      fcf_irr_r.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      eapply randomFunc_wf; eauto.
      fcf_sp.
      rewrite orb_true_r in *.
      simpl in *; discriminate.
      rewrite orb_true_r in *.
      simpl in *; discriminate.

      unfold randomFunc.
      splitOpt2;
      fcf_sp.
      splitIf; eqbTac.
      eauto.
      eapply H10; intuition idtac; subst; eqbTac.
      
      splitIf; fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      
      match goal with
      | [H : forall y, (y = ?a -> False) -> _ |- context[arrayLookup _ _ ?x]] =>
        case_eq (eqb x a); intros
      end; eqbTac.
      pairInv.
      match goal with
      | [H : (?a ?= ?b) = false |- _ ] =>
        replace a with b in *; eqbTac
      end.
      apply projectInfo_injective in H18.
      pairInv.
      intuition idtac.
      destruct c; simpl in *; f_equal.
      destruct p0; simpl in *; f_equal.
      apply app_eq_inv in H16.
      intuition idtac. subst.
      inversion H18; subst; trivial.
      eapply splitKdfInputs_length_eq_1; eauto.
      apply app_eq_inv in H19.
      intuition idtac. subst.
      inversion H18; subst; trivial.
      eapply splitKdfInputs_length_eq_2; eauto.
      destruct p1; simpl in *; f_equal.
      eapply splitKdfInputs_eq_inv; eauto.
      apply app_eq_inv in H16; intuition idtac.
      subst.
      apply app_eq_inv in H19; intuition idtac.
      subst.
      inversion H18; clear H18; subst.
      inversion H16; clear H16; subst.
      eapply lengthsCorrect_flatten_eq_inv in H17.
      apply app_eq_inv in H17; intuition idtac.
      inversion H16; clear H16; subst.
      reflexivity.
      eapply splitKdfInputs_length_eq_3; eauto.
      eapply splitKdfInputs_Some_app_lengthsCorrect; eauto.
      eapply splitKdfInputs_Some_app_lengthsCorrect; eauto.
      eapply splitKdfInputs_length_eq_2; eauto.
      eapply splitKdfInputs_length_eq_1; eauto.

      unfold randomFunc.
      splitOpt2; fcf_sp.
      splitIf; eqbTac.
      eauto.
      eapply H10; intuition idtac.
      rewrite H17 in H16. eqbTac.
      (* preserves bad *)
      intros.
      simp_in_support.
      eapply ccaOracle_G2_preserves_bad in H12; eauto.
      simp_in_support.
      simpl. trivial.
      intros.
      simp_in_support.
      eapply ccaOracle_G2_preserves_bad in H12; eauto.
      simp_in_support.
      simpl. trivial.
      
      intuition idtac.
      simpl.
      splitIf; eqbTac.
      reflexivity.
      
      simpl in *; fcf_sp.
    
      trivial.
      trivial.

      fcf_sp.
    Qed.

    Definition CtKDF_IND_CCA_bad_1 :=
      [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
      r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
      match r_opt with
      | None => ret ( false)
      | Some (s, R, a) =>
        p <-$ (A_KE P R) _ _ (randomFunc rndOKM _) nil;
        [ls, auxInfo, s_A] <-3 (fst p);
        st <- (snd p);
        match (splitKdfInputs additionalSecretLengths ls strongKE_Pos) with
        | None => ret (false)
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2) => 
          q <- (((flatten (s1 ++ s :: s2))), label,  (projectInfo ((Ps1 ++ P :: Ps2), (Rs1 ++ R :: Rs2), auxInfo)));
          bad <- if (arrayLookup _ st q) then true else false;
          [k, st'] <-$2 randomFunc rndOKM _ st q;
          p <-$ (OC_Run _ _ _ (A P ((P, R), (ls, auxInfo)) k (a, s_A)) (ccaOracle_G2 sk P ((P, R), (ls, auxInfo)) q) bad) _ _ (randomFunc rndOKM _) st';
          ret (snd (fst p))
        end
      end.

    Theorem CtKDF_IND_CCA_bad_1_equiv : 
      Pr [x <-$ CtKDF_IND_CCA_G1_0; ret (snd x) ] == Pr[CtKDF_IND_CCA_bad_1].

      unfold CtKDF_IND_CCA_G1_0, CtKDF_IND_CCA_bad_1.
      fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      
    Qed.

    Theorem CtKDF_IND_CCA_G2_close : 
      | Pr[CtKDF_IND_CCA_G1] - Pr[CtKDF_IND_CCA_G2] | <= Pr[CtKDF_IND_CCA_bad_1].

      rewrite CtKDF_IND_CCA_G1_0_equiv.
      rewrite <- CtKDF_IND_CCA_G1_1_G2_equiv.
      eapply leRat_trans.
      eapply fundamental_lemma_h.
      apply CtKDF_IND_CCA_G1_0_1_bad_eq.
      apply CtKDF_IND_CCA_G1_0_1_eq_until_bad.
      rewrite CtKDF_IND_CCA_bad_1_equiv.
      reflexivity.
    
    Qed.

    (* G2 is equivalent to the second INDCCA game *)
    Theorem CtKDF_IND_CCA_G2_equiv : 
      Pr [CtKDF_IND_CCA_G2] ==
      Pr [ExpROM _ _ rndOKM _ (KeyExchangeCCA_ROM_G1 _ _ A rndOKM) ].

      unfold CtKDF_IND_CCA_G2, ExpROM, KeyExchangeCCA_ROM_G1.
      fcf_sp.
      unfold ctKeyGen, HybridKE_Concatenate.ctKeyGen.
      fcf_sp.
      splitOpt; fcf_sp.
      fcf_skip.
      simpl.
      splitOpt; fcf_sp.
      fcf_swap leftc.
      fcf_skip.
      fcf_sp.
      fcf_skip.

      eapply (fcf_oracle_eq eq).
      reflexivity.
      intros; subst.
      unfold ccaOracle_G1, ccaOracle_ROM.
      unfold decapsFunc_ROM.
      simpl.
      splitQuery.
      fcf_sp.
      apply (cca_or_dec None).
      apply (cca_or_dec None).
      splitIf; fcf_sp.
      apply (cca_or_dec None).
      apply (cca_or_dec None).
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      apply (cca_or_dec None).
      apply (cca_or_dec None).
      simpl.
      fcf_sp.
      destruct b6; simpl in *; subst; trivial.
      destruct b6; simpl in *; subst; trivial.

    Qed.

     (* Remove the entry for the strong value from the state of the RO *)
    Definition CtKDF_IND_CCA_bad_2 :=
      [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
      r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
      match r_opt with
      | None => ret ( false)
      | Some (s, R, a) =>
        p <-$ (A_KE P R) _ _ (randomFunc rndOKM _) nil;
        [ls, auxInfo, s_A] <-3 (fst p);
        st <- (snd p);
        match (splitKdfInputs additionalSecretLengths ls strongKE_Pos) with
        | None => ret (false)
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2) => 
          q <- (((flatten (s1 ++ s :: s2))), label,  (projectInfo ((Ps1 ++ P :: Ps2), (Rs1 ++ R :: Rs2), auxInfo)));
          bad <- if (arrayLookup _ st q) then true else false;
          k <-$ rndOKM;
          p <-$ (OC_Run _ _ _ (A P ((P, R), (ls, auxInfo)) k (a, s_A)) (ccaOracle_G2 sk P ((P, R), (ls, auxInfo)) q) bad) _ _ (randomFunc rndOKM _) st;
          ret (snd (fst p))
        end
      end.

    Theorem CtKDF_IND_CCA_bad_2_equiv : 
      Pr[ CtKDF_IND_CCA_bad_1] == Pr[CtKDF_IND_CCA_bad_2].

      unfold CtKDF_IND_CCA_bad_1, CtKDF_IND_CCA_bad_2.
      fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      unfold randomFunc.
      splitOpt.
      (* goes bad *)
      fcf_sp.
      fcf_irr_l.
      repeat (try apply pair_EqDec; try apply list_EqDec; eauto with typeclass_instances).
      eapply oc_comp_wf; eauto.
      intros. wftac.
      eapply oc_comp_wf.
      apply ccaOracle_G2_wf.
      intros.
      eapply randomFunc_wf; eauto.
      fcf_irr_r.
      fcf_sp.
      fcf_irr_r.
      repeat (try apply pair_EqDec; try apply list_EqDec; eauto with typeclass_instances).
      eapply oc_comp_wf; eauto.
      intros. wftac.
      eapply oc_comp_wf.
      apply ccaOracle_G2_wf.
      intros.
      eapply randomFunc_wf; eauto.
      fcf_sp.
      destruct b5.
      eapply (oc_comp_invariant _ (fun x => (fst x) = true)) in H9.
      simpl in *.
      congruence.
      intros.
      repeat simp_in_support.
      simpl.
      eapply ccaOracle_G2_preserves_bad; eauto.
      simpl in *. trivial.
      destruct a1.
      eapply (oc_comp_invariant _ (fun x => (fst x) = true)) in H7.
      simpl in *.
      congruence.
      intros.
      repeat simp_in_support.
      simpl.
      eapply ccaOracle_G2_preserves_bad; eauto.
      simpl in *. trivial.

      fcf_sp.
      fcf_skip.
      match goal with
      | [|- context [ccaOracle_G2 _ _ _ ?a]] =>
       eapply (fcf_oracle_eq_until_bad (fun s => fst s) (fun s => fst s) (fun s1 s2 => forall x, x <>  a -> (arrayLookup _ (snd s1) x) = (arrayLookup _ (snd s2) x)))
      end.
      eauto.
      intros.
      wftac.
      apply oc_comp_wf.
      apply ccaOracle_G2_wf.
      intros.
      apply randomFunc_wf; eauto.
      intros.
      wftac.
      apply oc_comp_wf.
      apply ccaOracle_G2_wf.
      intros.
      apply randomFunc_wf; eauto.
      
      intros.
      match goal with 
      | [H : fst ?a = fst ?b |- _] =>
        destruct a; destruct b; simpl in *; subst
      end.
      unfold ccaOracle_G2.
      splitQuery; fcf_sp.
      splitOr_r; eqbTac.
      fcf_irr_l.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      eapply randomFunc_wf; eauto.
      fcf_irr_r.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      eapply randomFunc_wf; eauto.
      fcf_sp.
      rewrite orb_true_r in *.
      simpl in *; discriminate.
      rewrite orb_true_r in *.
      simpl in *; discriminate.

      unfold randomFunc.
      splitOpt2;
      fcf_sp.
      splitIf; eqbTac.
      eauto.
      eapply H9; intuition idtac; subst; eqbTac.
      
      splitIf; fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      
      match goal with
      | [H : forall y, (y = ?a -> False) -> _ |- context[arrayLookup _ _ ?x]] =>
        case_eq (eqb x a); intros
      end; eqbTac.
      pairInv.
      match goal with
      | [H : (?a ?= ?b) = false |- _ ] =>
        replace a with b in *; eqbTac
      end.
      apply projectInfo_injective in H17.
      pairInv.
      intuition idtac.
      destruct c; simpl in *; f_equal.
      destruct p0; simpl in *; f_equal.
      apply app_eq_inv in H15.
      intuition idtac.
      inversion H17; subst; trivial.
      eapply splitKdfInputs_length_eq_1; eauto.
      apply app_eq_inv in H18.
      intuition idtac.
      inversion H17; subst; trivial.
      eapply splitKdfInputs_length_eq_2; eauto.
      destruct p1; simpl in *; f_equal.
      eapply splitKdfInputs_eq_inv; eauto.
      apply app_eq_inv in H18; intuition idtac.
      subst.
      apply app_eq_inv in H15; intuition idtac.
      subst.
      inversion H17; clear H17; subst.
      inversion H18; clear H18; subst.
      eapply lengthsCorrect_flatten_eq_inv in H16.
      apply app_eq_inv in H16; intuition idtac.
      inversion H15; clear H15; subst.
      reflexivity.
      eapply splitKdfInputs_length_eq_3; eauto.
      eapply splitKdfInputs_Some_app_lengthsCorrect; eauto.
      eapply splitKdfInputs_Some_app_lengthsCorrect; eauto.
      eapply splitKdfInputs_length_eq_1; eauto.
      eapply splitKdfInputs_length_eq_2; eauto.

      splitOpt2; fcf_sp.
      splitIf; eqbTac.
      eauto.
      eapply H9; intuition idtac.
      rewrite H16 in H15. eqbTac.
      intros.
      simp_in_support.
      apply  ccaOracle_G2_preserves_bad in H11; trivial.
      simp_in_support.
      trivial.
      intros.
      simp_in_support.
      apply  ccaOracle_G2_preserves_bad in H11; trivial.
      simp_in_support.
      trivial.
      
      intuition idtac.
      simpl.
      splitIf; eqbTac.
      reflexivity.
      
      simpl in *; fcf_sp; trivial.

    Qed.

    (* Switch to a more structured random oracle to make it easier to work with the values associated with the strong KE. 
    Also, store the strong KE secret in the RO state as an option, since we want to remove it in later arguments. *)
    Definition DomainRO_split := (((((list BitString) * (option BitString) * (list BitString)) * BitString) * Salt * Info))%type.

    Definition RO_split_eq (s1 : list (DomainRO * RangeRO))(s2 : list (DomainRO_split * RangeRO)) :=
      forall secret salt info, 
      arrayLookup _ s1 (secret, salt, info) =
      arrayLookup _ s2 (splitSecrets secret, salt, info).

    Definition ccaOracle_bad_3(K : PrivateKey)(R : CtPublicResponse)(strongIKM : DomainRO_split)( bad : bool)(q : CCA_OracleQuery) :  OracleComp DomainRO_split RangeRO (CCA_OracleResponse  * bool) :=
    match q with
    | cca_oq_ro d => 
      [secret, salt, info] <-3 d;
      secrets <- splitSecrets secret;
      let d' : DomainRO_split := (secrets, salt, info) in
      r <--$ OC_Query _ d'; 
      $ret (cca_or_ro r, bad || (d' ?= strongIKM))
    | cca_oq_dec resp => 
      if (resp ?= R) then ($ret (cca_or_dec None, bad)) else
      r <--$ (
      s_opt <--$$ (@decapsFunc _ _ _ _ _ _ _ strongKE K (snd (fst resp)));
      match s_opt with
      | None => $ret (None, bad)
      | Some s => 
        match (splitKdfInputs additionalSecretLengths  (fst (snd resp)) strongKE_Pos) with
        | None => $ret (None, bad)
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  =>     
          q <- ((((s1, Some s, s2), nil)), label, (projectInfo ((Ps1 ++ (fst (fst resp)) :: Ps2), (Rs1 ++ (snd (fst resp)) :: Rs2), (snd (snd resp)))));
          k <--$ query q;
          $ret (Some k, bad)
        end
      end
      ); $ret (cca_or_dec (fst r), snd r)
    end.

    Definition randomFunc_split (st : list (DomainRO_split * RangeRO))(x : DomainRO) : Comp (RangeRO * list (DomainRO_split * RangeRO)) :=
      [secret, salt, info] <-3 x;
      secrets <- splitSecrets secret;
      randomFunc rndOKM _ st (secrets, salt , info).

    Definition CtKDF_IND_CCA_bad_3 :=
      [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
      r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
      match r_opt with
      | None => ret ( false)
      | Some (s, R, a) =>
        p <-$ (A_KE P R) _ _ randomFunc_split nil;
        [ls, auxInfo, s_A] <-3 (fst p);
        st <- (snd p);
        match (splitKdfInputs additionalSecretLengths ls strongKE_Pos) with
        | None => ret (false)
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2) => 
          q <- ((((s1, Some s, s2), nil)), label,  (projectInfo ((Ps1 ++ P :: Ps2), (Rs1 ++ R :: Rs2), auxInfo)));
          bad <- if (arrayLookup _ st q) then true else false;
          k <-$ rndOKM;
          p <-$ (OC_Run _ _ _ (A P ((P, R), (ls, auxInfo)) k (a, s_A)) (ccaOracle_bad_3 sk ((P, R), (ls, auxInfo)) q) bad) _ _ (randomFunc rndOKM _) st;
          ret (snd (fst p))
        end
      end.

    Theorem CtKDF_IND_CCA_bad_3_equiv : 
      Pr[CtKDF_IND_CCA_bad_2]== Pr[CtKDF_IND_CCA_bad_3].

      unfold CtKDF_IND_CCA_bad_2, CtKDF_IND_CCA_bad_3.
      specialize (well_formed_val_exists rndOKM_wf); intros.
      destruct H.
      fcf_sp.
      splitOpt; fcf_sp.
      fcf_skip.
      eapply (fcf_oracle_eq (fun s1 s2 =>  RO_split_eq s1 s2)).
      unfold RO_split_eq.
      intros.
      reflexivity.
      intuition idtac.
      unfold randomFunc_split.
      fcf_sp.
      unfold randomFunc.
      unfold RO_split_eq in *.
      match goal with
      | [|- comp_spec _ (match ?a with | Some _ => _ | None => _ end) (match ?b with | Some _ => _ | None => _ end) ] =>
        replace a with b; [case_eq b; intros | idtac]
      end.
      fcf_sp.
      Locate comp_spec_seq_eq.
      fcf_sp.
      splitIf; eqbTac.
      splitIf; eqbTac.
      splitIf; eqbTac.
      match goal with
      | [H: eqbPair ?a ?b ?c ?d = false |- _ ] =>
        replace c with d in *; eqbTac
      end.
      f_equal.
      f_equal.
      eapply splitSecrets_eq_inv; eauto.
      eauto.
      eauto.

      simpl in *.
      intuition idtac.
      destruct b5; simpl in *; subst.

      splitOpt; fcf_sp.
      fcf_skip.
      eapply (fcf_oracle_eq (fun s1 s2 => fst s1 = fst s2 /\ RO_split_eq (snd s1) (snd s2))).
      simpl; intuition idtac.
      unfold RO_split_eq in *.
      rewrite H8.
      unfold splitSecrets.
      rewrite toSecrets_flatten_eq.
      rewrite firstn_app_eq_gen.
      rewrite nth_middle_gen.
      rewrite skipn_app_cons_gen.
      unfold setLet.
      reflexivity.
      lengthTac.
      lengthTac.
      lengthTac.
      lengthTac.
      
      intuition idtac.
      simpl in *; subst.
      unfold ccaOracle_G2, ccaOracle_bad_3.
      splitQuery; fcf_sp.   
      unfold randomFunc.
      unfold RO_split_eq in *.
      splitOpt2; fcf_sp.
      f_equal.
      match goal with
      | [|- eqbPair ?a ?b ?c ?d = _ ] =>
        case_eq (eqbPair a b c d); intros; eqbTac
      end.
      unfold splitSecrets.
      rewrite toSecrets_flatten_eq.
      unfold setLet.
      rewrite firstn_app_eq_gen.
      rewrite skipn_app_cons_gen.
      rewrite nth_middle_gen.
      symmetry.
      apply eqbPair_refl.
      
      lengthTac.
      lengthTac.
      lengthTac.
      lengthTac.
      symmetry.
      match goal with
      | [|- eqbPair ?a ?b ?c ?d = _ ] =>
        case_eq (eqbPair a b c d); intros; eqbTac
      end.
      match goal with
      | [H: eqbPair ?a ?b ?c ?d = false |- _ ] =>
        replace c with d in *; eqbTac
      end.
      f_equal. f_equal.
      symmetry.
      eapply splitSecrets_eq_inv.
      rewrite H15.
      unfold splitSecrets.
      rewrite toSecrets_flatten_eq.
      unfold setLet.
      rewrite firstn_app_eq_gen.
      rewrite nth_middle_gen.
      rewrite skipn_app_cons_gen.
      reflexivity.
      lengthTac.
      lengthTac.
      lengthTac.
      lengthTac.

      f_equal.
      match goal with
      | [|- eqbPair ?a ?b ?c ?d = _ ] =>
        case_eq (eqbPair a b c d); intros; eqbTac
      end.
      unfold splitSecrets.
      rewrite toSecrets_flatten_eq.
      unfold setLet.
      rewrite firstn_app_eq_gen.
      rewrite skipn_app_cons_gen.
      rewrite nth_middle_gen.
      symmetry.
      apply eqbPair_refl.
      
      lengthTac.
      lengthTac.
      lengthTac.
      lengthTac.
      symmetry.
      match goal with
      | [|- eqbPair ?a ?b ?c ?d = _ ] =>
        case_eq (eqbPair a b c d); intros; eqbTac
      end.
      match goal with
      | [H: eqbPair ?a ?b ?c ?d = false |- _ ] =>
        replace c with d in *; eqbTac
      end.
      f_equal. f_equal.
      symmetry.
      eapply splitSecrets_eq_inv.
      rewrite H17.
      unfold splitSecrets.
      rewrite toSecrets_flatten_eq.
      unfold setLet.
      rewrite firstn_app_eq_gen.
      rewrite nth_middle_gen.
      rewrite skipn_app_cons_gen.
      reflexivity.
      lengthTac.
      lengthTac.
      lengthTac.
      lengthTac.

      splitIf; eqbTac.
      splitIf; eqbTac.
      splitIf; eqbTac.
      match goal with
      | [H: eqbPair ?a ?b ?c ?d = false |- _ ] =>
        replace c with d in *; eqbTac
      end.
      f_equal. f_equal.
      eapply splitSecrets_eq_inv.
      symmetry.
      trivial.
      eauto.
      eauto.

      splitIf; fcf_sp.
      splitOpt; fcf_sp.
      subst.
      splitOpt; fcf_sp.
      unfold randomFunc.
      splitOpt2; fcf_sp.

      unfold RO_split_eq.
      intros.
      simpl.
      splitIf; eqbTac.
      splitIf; eqbTac.
      match goal with
      | [H: eqbPair ?a ?b ?c ?d = false |- _ ] =>
        replace c with d in *; eqbTac
      end.
      f_equal.
      f_equal.
      f_equal.
      unfold splitSecrets.
      rewrite toSecrets_flatten_eq.   
      unfold setLet.
      rewrite firstn_app_eq_gen.
      rewrite nth_middle_gen.
      rewrite skipn_app_cons_gen.
      reflexivity.
      lengthTac.
      lengthTac.
      lengthTac.
      lengthTac.
      splitIf; eqbTac.
      match goal with
      | [H: eqbPair ?a ?b ?c ?d = false |- _ ] =>
        replace c with d in *; eqbTac
      end.
      f_equal.
      f_equal.
      symmetry.
      eapply splitSecrets_eq_inv.
      rewrite H21.
      unfold splitSecrets.
      rewrite toSecrets_flatten_eq.
      unfold setLet.
      rewrite firstn_app_eq_gen.
      rewrite nth_middle_gen.
      rewrite skipn_app_cons_gen.
      reflexivity.
      lengthTac.
      lengthTac.
      lengthTac.
      lengthTac.
      apply H12.
      simpl.      
      unfold RO_split_eq in *.
      rewrite H12.
      unfold splitSecrets.
      rewrite toSecrets_flatten_eq.
      unfold setLet.
      rewrite firstn_app_eq_gen.
      rewrite nth_middle_gen.
      rewrite skipn_app_cons_gen.
      reflexivity.
      lengthTac.
      lengthTac.
      lengthTac.
      lengthTac.

      simpl in *; fcf_sp; trivial.
    Qed.

    (* Don't query the decaps function on the challenge---use the secret returned by the response function instead *)
    Definition ccaOracle_bad_4(K : PrivateKey)(R : CtPublicResponse)(strongIKM : DomainRO_split)(strongSecret : BitString)( bad : bool)(q : CCA_OracleQuery) :  OracleComp DomainRO_split RangeRO (CCA_OracleResponse  * bool) :=
    match q with
    | cca_oq_ro d => 
      [secret, salt, info] <-3 d;
      secrets <- splitSecrets secret;
      let d' : DomainRO_split := (secrets, salt, info) in
      r <--$ OC_Query _ d'; 
      $ret (cca_or_ro r, bad || (d' ?= strongIKM))
    | cca_oq_dec resp => 
      if (resp ?= R) then ($ret (cca_or_dec None, bad)) else
      r <--$ (
      s_opt <--$$ if (eqb (snd (fst resp)) (snd (fst R))) then ret (Some strongSecret) else (@decapsFunc _ _ _ _ _ _ _ strongKE K (snd (fst resp)));
      match s_opt with
      | None => $ret (None, bad)
      | Some s => 
        match (splitKdfInputs additionalSecretLengths (fst (snd resp)) strongKE_Pos) with
        | None => $ret (None, bad)
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  =>     
          q <- ((((s1, Some s, s2), nil)), label, (projectInfo ((Ps1 ++ (fst (fst resp)) :: Ps2), (Rs1 ++ (snd (fst resp)) :: Rs2), (snd (snd resp)))));
          k <--$ query q;
          $ret (Some k, bad)
        end
      end
      ); $ret (cca_or_dec (fst r), snd r)
    end.

    Definition CtKDF_IND_CCA_bad_4 :=
      [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
      r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
      match r_opt with
      | None => ret false
      | Some (s, R, a) =>
        p <-$ (A_KE P R) _ _ randomFunc_split nil;
        [ls, auxInfo, s_A] <-3 (fst p);
        st <- (snd p);
        match (splitKdfInputs additionalSecretLengths ls strongKE_Pos)  with
        | None => ret false
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  => 
          q <- ((((s1, Some s, s2), nil)), label,  (projectInfo ((Ps1 ++ P :: Ps2), (Rs1 ++ R :: Rs2), auxInfo)));
          bad <- if (arrayLookup _ st q) then true else false;
          k <-$ rndOKM;
          p <-$ ((
          R <- ((P, R), (ls, auxInfo));
          OC_Run _ _ _ (A P R k (a, s_A)) (ccaOracle_bad_4 sk R q s) bad) _ _ (randomFunc rndOKM _) st);
          ret (snd (fst p))
        end
      end.

    (* Identical until bad---expose the bad event *)
    Definition CtKDF_IND_CCA_bad_4_0 :=
      [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
      r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
      match r_opt with
      | None => ret (false, false)
      | Some (s, R, a) =>
        s' <-$ (@decapsFunc _ _ _ _ _ _ _ strongKE sk R);
        p <-$ (A_KE P R) _ _ randomFunc_split nil;
        [ls, auxInfo, s_A] <-3 (fst p);
        st <- (snd p);
        match (splitKdfInputs additionalSecretLengths ls strongKE_Pos)  with
        | None => ret (false, false)
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  => 
          q <- ((((s1, Some s, s2), nil)), label,  (projectInfo ((Ps1 ++ P :: Ps2), (Rs1 ++ R :: Rs2), auxInfo)));
          bad <- if (arrayLookup _ st q) then true else false;
          k <-$ rndOKM;
          p <-$ ((
          OC_Run _ _ _ (A P ((P, R), (ls, auxInfo)) k (a, s_A)) (ccaOracle_bad_3 sk ((P, R), (ls, auxInfo)) q) bad) _ _ (randomFunc rndOKM _) st);
          ret (snd (fst p), negb (eqb (Some s) s'))
        end
      end.

    Definition CtKDF_IND_CCA_bad_4_1 :=
      [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
      r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
      match r_opt with
      | None => ret (false, false)
      | Some (s, R, a) =>
        s' <-$ (@decapsFunc _ _ _ _ _ _ _ strongKE sk R);
        p <-$ (A_KE P R) _ _ randomFunc_split nil;
        [ls, auxInfo, s_A] <-3 (fst p);
        st <- (snd p);
        match (splitKdfInputs additionalSecretLengths ls strongKE_Pos)  with
        | None => ret (false, false)
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  => 
          q <- ((((s1, Some s, s2), nil)), label,  (projectInfo ((Ps1 ++ P :: Ps2), (Rs1 ++ R :: Rs2), auxInfo)));
          bad <- if (arrayLookup _ st q) then true else false;
          k <-$ rndOKM;
          p <-$ ((
          R <- ((P, R), (ls, auxInfo));
          OC_Run _ _ _ (A P R k (a, s_A)) (ccaOracle_bad_4 sk R q s) bad) _ _ (randomFunc rndOKM _) st);
          ret (snd (fst p), negb (eqb (Some s) s'))
        end
      end.

    Theorem CtKDF_IND_CCA_bad_3_4_0_equiv : 
        Pr[CtKDF_IND_CCA_bad_3] == Pr[x <-$ CtKDF_IND_CCA_bad_4_0; ret (fst x)].
    
      unfold CtKDF_IND_CCA_bad_3, CtKDF_IND_CCA_bad_4_0.
      fcf_sp.
      splitOpt; fcf_sp.
      fcf_irr_r. 
      apply option_EqDec; eauto with typeclass_instances. 
      fcf_sp.
      splitOpt; fcf_sp.
      
    Qed.

    Theorem CtKDF_IND_CCA_bad_4_1_4_equiv : 
        Pr[CtKDF_IND_CCA_bad_4] == Pr[x <-$ CtKDF_IND_CCA_bad_4_1; ret (fst x)].

      unfold CtKDF_IND_CCA_bad_4, CtKDF_IND_CCA_bad_4_1.
      fcf_sp.
      splitOpt; fcf_sp.
      fcf_irr_r. 
      apply option_EqDec; eauto with typeclass_instances. 
      fcf_sp.
      splitOpt; fcf_sp.

    Qed.

    Theorem ccaOracle_bad_3_wf : forall a b c d e,
      well_formed_oc
        (ccaOracle_bad_3 a b c d e).

      intros.
      unfold ccaOracle_bad_3.
      splitQuery; wftac.
      destruct d0; wftac.
      splitIf; wftac.
      intros.
      splitOpt; wftac.
      splitOpt; wftac.
      destruct p. destruct p. destruct p. destruct p. destruct p. 
      wftac.

    Qed.

    Theorem ccaOracle_bad_4_wf : forall a b c d e f,
      well_formed_oc
        (ccaOracle_bad_4 a b c d e f).

      intros.
      unfold ccaOracle_bad_4.
      splitQuery; wftac.
      destruct d0; wftac.
      splitIf; wftac.
      intros.
      splitOpt; wftac.
      splitOpt; wftac.
      destruct p. destruct p. destruct p. destruct p. destruct p. 
      wftac.

    Qed.

    Theorem CtKDF_IND_CCA_bad_4_0_1_eq_until_bad : forall x,
      evalDist CtKDF_IND_CCA_bad_4_0 (x, false) == evalDist CtKDF_IND_CCA_bad_4_1 (x, false).

      intros.
      unfold CtKDF_IND_CCA_bad_4_0, CtKDF_IND_CCA_bad_4_1.
      fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      case_eq (Some b1 ?= b2); intros; eqbTac.
      fcf_skip.
      eapply (fcf_oracle_eq eq); trivial; intros.
      unfold ccaOracle_bad_3, ccaOracle_bad_4.
      splitQuery; fcf_sp.
      splitIf; fcf_sp.
      splitIf; fcf_sp.
      fcf_irr_l.
      apply option_EqDec; eauto with typeclass_instances.
      fcf_sp.
      splitOpt; fcf_sp.
      subst.
      splitOpt; fcf_sp.
      destruct c; simpl in *.
      eqbTac.
      replace (Some b1) with (Some b6).
      fcf_sp.
      eapply strongDecaps_deterministic; eauto.
      subst.
      destruct c; simpl in *.
      eqbTac.
      simpl in *.
      assert (Some b1 = None).
      eapply strongDecaps_deterministic; eauto.
      discriminate.
      simpl in *; fcf_sp.
      destruct b2; simpl in *; subst; pairInv; trivial.
      destruct b2; simpl in *; subst; pairInv; trivial.

      fcf_irr_l.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      apply oc_comp_wf; eauto; intros.
      wftac.
      apply oc_comp_wf.
      apply ccaOracle_bad_3_wf.
      apply randomFunc_wf; eauto.
      fcf_irr_r.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      apply oc_comp_wf; eauto; intros.
      wftac.
      apply oc_comp_wf.
      apply ccaOracle_bad_4_wf.
      apply randomFunc_wf; eauto.
      fcf_sp.
      pairInv.
      pairInv.

    Qed.

    Theorem CtKDF_IND_CCA_bad_4_0_1_bad_eq : 
        Pr[x <-$ CtKDF_IND_CCA_bad_4_0; ret (snd x)] == Pr[x <-$ CtKDF_IND_CCA_bad_4_1; ret (snd x)].

      intros.
      unfold CtKDF_IND_CCA_bad_4_0, CtKDF_IND_CCA_bad_4_1.
      fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.

      fcf_irr_l.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      apply oc_comp_wf; eauto; intros.
      wftac.
      apply oc_comp_wf.
      apply ccaOracle_bad_3_wf.
      apply randomFunc_wf; eauto.
      fcf_irr_r.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      apply oc_comp_wf; eauto; intros.
      wftac.
      apply oc_comp_wf.
      apply ccaOracle_bad_4_wf.
      apply randomFunc_wf; eauto.
      fcf_sp.

    Qed.

    Theorem CtKDF_IND_CCA_bad_4_0_eq_correctnessError : 
      Pr [x <-$ CtKDF_IND_CCA_bad_4_0; ret snd x ] <= strongKE_correctnessError.

      unfold CtKDF_IND_CCA_bad_4_0, strongKE_correctnessError, KE_CorrectnessError, KE_Correctness_G.
      eapply comp_spec_impl_le.
      fcf_sp.
      splitOpt; fcf_sp.
      fcf_irr_l; fcf_sp.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      eapply oc_comp_wf; eauto.
      intros.
      unfold randomFunc_split; wftac.
      destruct p0.
      apply randomFunc_wf; eauto.
      splitOpt; fcf_sp.
      fcf_irr_l; fcf_sp.
      fcf_irr_l; fcf_sp.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      apply oc_comp_wf; eauto; intros.
      wftac.
      apply oc_comp_wf.
      apply ccaOracle_bad_3_wf.
      apply randomFunc_wf; eauto.
      discriminate.

    Qed.

    Theorem CtKDF_IND_CCA_bad_4_close : 
      | Pr[CtKDF_IND_CCA_bad_3] - Pr[CtKDF_IND_CCA_bad_4] | <= strongKE_correctnessError.

      eapply leRat_trans.
      rewrite CtKDF_IND_CCA_bad_3_4_0_equiv.
      rewrite CtKDF_IND_CCA_bad_4_1_4_equiv.
      eapply fundamental_lemma_h.
      apply CtKDF_IND_CCA_bad_4_0_1_bad_eq.
      apply CtKDF_IND_CCA_bad_4_0_1_eq_until_bad.
      apply CtKDF_IND_CCA_bad_4_0_eq_correctnessError.
    Qed.

    (* go bad any time the RO is queried using the strong secret, except on a decrypt query containing the strong response value *)
    Definition ccaOracle_bad_5(K : PrivateKey)(R : CtPublicResponse)(strongSecret : BitString)( bad : bool)(q : CCA_OracleQuery) :  OracleComp DomainRO_split RangeRO (CCA_OracleResponse  * bool) :=
    match q with
    | cca_oq_ro d => 
      [secret, salt, info] <-3 d;
      secrets <- splitSecrets secret;
      let d' : DomainRO_split := (secrets, salt, info) in
      r <--$ OC_Query _ d'; 
      $ret (cca_or_ro r, bad || (snd (fst (fst secrets)) ?= Some strongSecret))
    | cca_oq_dec resp => 
      if (resp ?= R) then ($ret (cca_or_dec None, bad)) else
      r <--$ (
      s_opt <--$$ if (eqb (snd (fst resp)) (snd (fst R))) then ret (Some strongSecret) else (@decapsFunc _ _ _ _ _ _ _ strongKE K (snd (fst resp)));
      match s_opt with
      | None => $ret (None, bad)
      | Some s => 
        match (splitKdfInputs additionalSecretLengths (fst (snd resp)) strongKE_Pos) with
        | None => $ret (None, bad)
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  =>     
          q <- ((((s1, Some s, s2), nil)), label, (projectInfo ((Ps1 ++ (fst (fst resp)) :: Ps2), (Rs1 ++ (snd (fst resp)) :: Rs2), (snd (snd resp)))));
          k <--$ query q;
          $ret (Some k, bad || ((s ?= strongSecret) && (negb ((snd (fst resp)) ?= (snd (fst R))))))
        end
      end
      ); $ret (cca_or_dec (fst r), snd r)
    end.

   Definition CtKDF_IND_CCA_bad_5 :=
      [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
      r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
      match r_opt with
      | None => ret false
      | Some (s, R, a) =>
        p <-$ (A_KE P R) _ _ randomFunc_split nil;
        [ls, auxInfo, s_A] <-3 (fst p);
        st <- (snd p);
        match (splitKdfInputs additionalSecretLengths ls strongKE_Pos)  with
        | None => ret false
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  => 
          bad <- (any_dec (eqb (Some s)) (map (fun x => snd (fst (fst (fst (fst x))))) (fst (split st))));
          k <-$ rndOKM;
          p <-$ ((
          R <- ((P, R), (ls, auxInfo));
          OC_Run _ _ _ (A P R k (a, s_A)) (ccaOracle_bad_5 sk R  s) bad) _ _ (randomFunc rndOKM _) st);
          ret (snd (fst p))
        end
      end.

     Theorem CtKDF_IND_CCA_bad_4_le_5 : 
      Pr[CtKDF_IND_CCA_bad_4] <= Pr[CtKDF_IND_CCA_bad_5].
    
      unfold CtKDF_IND_CCA_bad_4, CtKDF_IND_CCA_bad_5.
      eapply comp_spec_impl_le.
      fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      fcf_skip.
      eapply (fcf_oracle_eq (fun s1 s2 => snd s1 = snd s2 /\ (fst s1 = true -> fst s2 = true))).
      intuition idtac; simpl in *; trivial.
      rewrite <- any_dec_eq_arrayLookup in H8.
      rewrite <- any_dec_map.
      apply any_dec_ex in H8.
      destruct H8.
      intuition idtac; eqbTac.
      eapply ex_any_dec; eauto.
      simpl.
      apply eqb_refl.

      intuition idtac.
      simpl in *; subst.
      unfold ccaOracle_bad_4, ccaOracle_bad_5.
      splitQuery; fcf_sp.
      apply orb_prop in H11; intuition idtac.
      rewrite H11. reflexivity.
      eqbTac.
      rewrite H13. simpl.
      rewrite eqb_refl.
      apply orb_true_r.
      
      splitIf; fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      rewrite H16.
      reflexivity.
      simpl in *; fcf_sp.

    Qed.


    (* in the decrypt query, query the RO on None instead of (Some strongSecret) *)
    Definition ccaOracle_bad_6(K : PrivateKey)(R : CtPublicResponse)(strongSecret : BitString)( bad : bool)(q : CCA_OracleQuery) :  OracleComp DomainRO_split RangeRO (CCA_OracleResponse  * bool) :=
    match q with
    | cca_oq_ro d => 
      [secret, salt, info] <-3 d;
      secrets <- splitSecrets secret;
      let d' : DomainRO_split := (secrets, salt, info) in
      r <--$ OC_Query _ d'; 
      $ret (cca_or_ro r, bad || (snd (fst (fst secrets)) ?= Some strongSecret))
    | cca_oq_dec resp => 
      if (resp ?= R) then ($ret (cca_or_dec None, bad)) else
      r <--$ (
      s_opt <--$$ if (eqb (snd (fst resp)) (snd (fst R))) then ret (Some nil) else (@decapsFunc _ _ _ _ _ _ _ strongKE K (snd (fst resp)));
      match s_opt with
      | None => $ret (None, bad)
      | Some s => 
        match (splitKdfInputs additionalSecretLengths (fst (snd resp)) strongKE_Pos) with
        | None => $ret (None, bad)
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  =>     
          s' <- if (eqb (snd (fst resp)) (snd (fst R))) then None else (Some s);
          q <- ((((s1, s', s2), nil)), label, (projectInfo ((Ps1 ++ (fst (fst resp)) :: Ps2), (Rs1 ++ (snd (fst resp)) :: Rs2), (snd (snd resp)))));
          k <--$ query q;
          $ret (Some k, bad || ((s ?= strongSecret) && (negb ((snd (fst resp)) ?= (snd (fst R))))))
        end
      end
      ); $ret (cca_or_dec (fst r), snd r)
    end.

    Definition CtKDF_IND_CCA_bad_6 :=
      [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
      r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
      match r_opt with
      | None => ret false
      | Some (s, R, a) =>
        p <-$ (A_KE P R) _ _ randomFunc_split nil;
        [ls, auxInfo, s_A] <-3 (fst p);
        st <- (snd p);
        match (splitKdfInputs additionalSecretLengths ls strongKE_Pos)  with
        | None => ret false
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  => 
          bad <- (any_dec (eqb (Some s)) (map (fun x => snd (fst (fst (fst (fst x))))) (fst (split st))));
          k <-$ rndOKM;
          p <-$ ((
          R <- ((P, R), (ls, auxInfo));
          OC_Run _ _ _ (A P R k (a, s_A)) (ccaOracle_bad_6 sk R  s) bad) _ _ (randomFunc rndOKM _) st);
          ret (snd (fst p))
        end
      end.


    Theorem ccaOracle_bad_5_wf : forall a b c d e,
      well_formed_oc (ccaOracle_bad_5 a b c d e).

      intros.
      unfold ccaOracle_bad_5.
      splitQuery; wftac.
      destruct d0; wftac.
      splitIf; wftac.
      intros.
      splitOpt; wftac.
      splitOpt; wftac.
      destruct p. destruct p. destruct p. destruct p. destruct p. 
      wftac.

    Qed.

    Theorem ccaOracle_bad_6_wf : forall a b c d e,
      well_formed_oc (ccaOracle_bad_6 a b c d e).

      intros.
      unfold ccaOracle_bad_6.
      splitQuery; wftac.
      destruct d0; wftac.
      splitIf; wftac.
      intros.
      splitOpt; wftac.
      splitOpt; wftac.
      destruct p. destruct p. destruct p. destruct p. destruct p. 
      wftac.

    Qed.

    Theorem ccaOracle_bad_5_preserves_bad : forall (S : Set)(eqdS : EqDec S) x a b c (e : bool)(f : CCA_OracleQuery)(g : S -> DomainRO_split -> Comp (RangeRO * S)) s,
      e = true ->
      In x (getSupport (ccaOracle_bad_5 a b c e f _ _ g s)) ->
      snd (fst x) = true.

      intros.
      unfold ccaOracle_bad_5 in *.
      destruct f; simpl in *; repeat simp_in_support.
      destruct d.
      destruct p.
      simpl in *; repeat simp_in_support.
      destruct x0; simpl in *; repeat simp_in_support.
      reflexivity.
      
      destruct  (c0 ?= b); simpl in *; repeat simp_in_support.
      reflexivity.
      destruct (splitKdfInputs additionalSecretLengths (fst (snd c0)) strongKE_Pos); simpl in *; repeat simp_in_support.
      destruct p. destruct p. destruct p. destruct p. destruct p.
      simpl in *; repeat simp_in_support.
      destruct x1; repeat simp_in_support.
      reflexivity.
      reflexivity.
      destruct x2; simpl in *; repeat simp_in_support.
      destruct (splitKdfInputs additionalSecretLengths (fst (snd c0)) strongKE_Pos); simpl in *; repeat simp_in_support.
      destruct p. destruct p. destruct p. destruct p. destruct p.
      simpl in *; repeat simp_in_support.
      destruct x1; repeat simp_in_support.
      reflexivity.
      reflexivity.
      reflexivity.

    Qed.

    Theorem ccaOracle_bad_6_preserves_bad : forall (S : Set)(eqdS : EqDec S) x a b c (e : bool)(f : CCA_OracleQuery)(g : S -> DomainRO_split -> Comp (RangeRO * S)) s,
      e = true ->
      In x (getSupport (ccaOracle_bad_6 a b c e f _ _ g s)) ->
      snd (fst x) = true.

      intros.
      unfold ccaOracle_bad_6 in *.
      destruct f; simpl in *; repeat simp_in_support.
      destruct d.
      destruct p.
      simpl in *; repeat simp_in_support.
      destruct x0; simpl in *; repeat simp_in_support.
      reflexivity.
      
      destruct  (c0 ?= b); simpl in *; repeat simp_in_support.
      reflexivity.
      destruct (splitKdfInputs additionalSecretLengths (fst (snd c0)) strongKE_Pos); simpl in *; repeat simp_in_support.
      destruct p. destruct p. destruct p. destruct p. destruct p.
      simpl in *; repeat simp_in_support.
      destruct x1; repeat simp_in_support.
      reflexivity.
      reflexivity.
      destruct x2; simpl in *; repeat simp_in_support.
      destruct (splitKdfInputs additionalSecretLengths (fst (snd c0)) strongKE_Pos); simpl in *; repeat simp_in_support.
      destruct p. destruct p. destruct p. destruct p. destruct p.
      simpl in *; repeat simp_in_support.
      destruct x1; repeat simp_in_support.
      reflexivity.
      reflexivity.
      reflexivity.

    Qed.

    Theorem any_dec_false_forall : 
      forall (A : Set)(f : A -> bool) ls,
        any_dec f ls = false ->
        (forall a, In a ls -> f a = false).

      induction ls; intros; simpl in *; intuition idtac.
      subst. rewrite any_dec_cons in *.
      apply orb_false_elim in H.
      intuition idtac; trivial.
      rewrite any_dec_cons in *.
      apply orb_false_elim in H.
      intuition idtac; trivial.
      eapply H; eauto.

    Qed.

    Theorem CtKDF_IND_CCA_bad_6_equiv : 
      Pr[CtKDF_IND_CCA_bad_5] == Pr[CtKDF_IND_CCA_bad_6].

      unfold CtKDF_IND_CCA_bad_5, CtKDF_IND_CCA_bad_6.
      fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      match goal with 
      | [|- context[any_dec ?a ?b]] =>
        case_eq (any_dec a b); intros
      end.
      (* goes bad *)
      fcf_sp.
      fcf_irr_l.
      repeat (try apply pair_EqDec; try apply list_EqDec; eauto with typeclass_instances).
      eapply oc_comp_wf; eauto.
      intros. wftac.
      eapply oc_comp_wf.
      apply ccaOracle_bad_5_wf.
      intros.
      eapply randomFunc_wf; eauto.
      fcf_irr_r.
      repeat (try apply pair_EqDec; try apply list_EqDec; eauto with typeclass_instances).
      eapply oc_comp_wf; eauto.
      intros. wftac.
      eapply oc_comp_wf.
      apply ccaOracle_bad_6_wf.
      intros.
      eapply randomFunc_wf; eauto.
      fcf_sp.
      destruct b5.
      eapply (oc_comp_invariant _ (fun x => (fst x) = true)) in H10.
      simpl in *.
      congruence.
      intros.
      repeat simp_in_support.
      simpl.
      eapply ccaOracle_bad_6_preserves_bad; eauto.
      simpl in *. trivial.
      destruct a1.
      eapply (oc_comp_invariant _ (fun x => (fst x) = true)) in H9.
      simpl in *.
      congruence.
      intros.
      repeat simp_in_support.
      simpl.
      eapply ccaOracle_bad_5_preserves_bad; eauto.
      simpl in *. trivial.
     
      fcf_skip.
      match goal with
      | [|- context[ccaOracle_bad_6 _ _ ?sec]] =>
        eapply (fcf_oracle_eq_until_bad (fun s => fst s) (fun s => fst s) 
          (fun s1 s2 => 
            (forall (x : DomainRO_split), (snd (fst (fst (fst (fst x))))) <> Some sec -> (snd (fst (fst (fst (fst x))))) <> None -> arrayLookup _ (snd s1) x = arrayLookup _ (snd s2) x) /\
            (forall x y z b c, arrayLookup _ (snd s1) ((x, (Some sec), y, z), b, c) = arrayLookup _ (snd s2) ((x, None, y, z), b, c)) 
            )
        )
      end.
      eauto.
      intros.
      wftac.
      apply oc_comp_wf.
      apply ccaOracle_bad_5_wf.
      intros.
      apply randomFunc_wf; eauto.
      intros.
      wftac.
      apply oc_comp_wf.
      apply ccaOracle_bad_6_wf.
      intros.
      apply randomFunc_wf; eauto.

      intros.
      destruct x1. destruct x2. simpl in *. subst.
      intuition idtac.
      unfold ccaOracle_bad_5, ccaOracle_bad_6.
      splitQuery; fcf_sp.
      splitOr_r; eqbTac; fcf_sp.
      fcf_irr_l.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      apply randomFunc_wf; eauto.
      fcf_irr_r.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      apply randomFunc_wf; eauto.
      fcf_sp.
      rewrite orb_true_r in *. discriminate.
      rewrite orb_true_r in *. discriminate.
      rewrite orb_true_r in *. discriminate.

      unfold randomFunc.
      splitOpt2; fcf_sp.
      splitIf; eqbTac.
      eapply H10; intuition idtac.
      splitIf; eqbTac.
      rewrite <- H18 in H9.
      simpl in *.
      eqbTac.
      splitIf; eqbTac.
      unfold splitSecrets in *.
      destruct (toSecrets b5).
      unfold setLet in *.
      simpl in *.
      discriminate.
      eapply H11; intuition idtac.
      eapply H10; intuition idtac.
      simpl in *.
      rewrite H12 in H9. eqbTac.
      simpl in *.
      unfold splitSecrets in *.
      destruct (toSecrets b5).
      unfold setLet in *.
      simpl in *. discriminate.
      
      splitIf; fcf_sp.
      splitOpt; fcf_sp.
      splitIf; fcf_sp.
      destruct c; simpl in *.
      eqbTac.
      unfold randomFunc.
      splitOpt2; fcf_sp.
      repeat rewrite eqb_refl; simpl.
      repeat rewrite andb_false_r; reflexivity.
      repeat rewrite eqb_refl; simpl.
      repeat rewrite andb_false_r; reflexivity.
      splitIf; eqbTac.
      splitIf; eqbTac.
      eapply H10; intuition idtac.
      splitIf; eqbTac.
      splitIf; eqbTac.
      rewrite eqbPair_refl in *.
      discriminate.
      splitIf; eqbTac.
      rewrite eqbPair_refl in *.
      discriminate.
      apply H11.
      apply H11.
      splitOpt; fcf_sp.
      subst.
      case_eq (eqb l13 b1); intros; eqbTac.
      fcf_irr_l; fcf_sp.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      apply randomFunc_wf; eauto.
      fcf_irr_r; fcf_sp.
      repeat (try apply pair_EqDec; try apply list_EqDec); eauto with typeclass_instances.
      apply randomFunc_wf; eauto.
      rewrite eqb_refl. simpl.
      reflexivity.

      destruct c; simpl in *; subst.
      destruct p0; simpl in *; subst.
      case_eq (p2 ?= p); intros; eqbTac;
      repeat rewrite eqb_refl in *; simpl in *.
      rewrite orb_true_r in *. discriminate.
      rewrite eqb_refl in *; simpl in *.
      rewrite orb_true_r in *. discriminate.
      rewrite eqb_refl in *; simpl in *.
      rewrite orb_true_r in *. discriminate.
 
      unfold randomFunc.
      splitOpt2; fcf_sp.
      rewrite andb_true_r.
      splitOr_r; eqbTac.
      rewrite andb_true_r.
      splitOr_r; eqbTac.
      splitIf; eqbTac.
      simpl in *.
      splitIf; eqbTac.
      rewrite eqbPair_refl in *.
      discriminate.
      splitIf; eqbTac.
      rewrite eqbPair_refl in *.
      discriminate.
      apply H10; intuition idtac.
      splitIf; eqbTac.
      splitIf; eqbTac.
      apply H11.
      apply H10; intuition idtac.
      simpl in *.
      inversion H17; clear H17; subst; eqbTac.
      simpl in *.
      discriminate.

      splitIf; fcf_sp.
      splitOpt; fcf_sp.

      intros.
      simp_in_support.
      apply ccaOracle_bad_5_preserves_bad in H11; trivial.
      repeat simp_in_support.
      trivial.
      intros.
      simp_in_support.
      apply ccaOracle_bad_6_preserves_bad in H11; trivial.
      repeat simp_in_support.
      trivial.

      intuition idtac.
      simpl.
      repeat rewrite notInArrayLookupNone.
      reflexivity.
      intuition idtac.
      eapply (oc_comp_invariant _ (fun x => forall y, (In y (fst (split x)) -> (snd (fst (fst (fst (fst y)))) <> None)))) in H5.
      eapply H5.
      assert (snd (fst (fst (fst (fst (x, (@None BitString), y, z, b5, c))))) = None).
      reflexivity.
      apply H10.
      intuition idtac.
      unfold randomFunc_split in *.
      unfold setLet in *.
      destruct d.
      destruct p0.
      unfold randomFunc in *.
      match goal with
      | [H: In _ (getSupport (match ?a with | Some _ => _ | None => _ end)) |- _ ] =>
        case_eq a; intros
      end;
      rewrite H14 in H10;
      repeat simp_in_support.
      eapply H11.
      eauto.
      trivial.
      simpl in *; intuition idtac.
      remember (split c0) as z1. destruct z1.
      simpl in *.
      intuition idtac.
      subst.
      unfold splitSecrets in *.
      destruct (toSecrets b7).
      simpl in *.
      discriminate.
      eapply H11.
      eauto.
      trivial.
      intuition idtac.
      trivial.

      intuition idtac.
      rewrite <- any_dec_map in *.
      eapply any_dec_false_forall in H8; eauto.
      simpl in *.
      rewrite eqb_refl in H8.
      discriminate.

      reflexivity.
      fcf_sp;
      congruence.

    Qed.

    (* Use the presence of the strong secret in the RO state to determine when the game has gone bad *)
    Definition ccaOracle_bad_7(K : PrivateKey)(R : CtPublicResponse)( _ : unit)(q : CCA_OracleQuery) :  OracleComp DomainRO_split RangeRO (CCA_OracleResponse  * unit) :=
    match q with
    | cca_oq_ro d => 
      [secret, salt, info] <-3 d;
      secrets <- splitSecrets secret;
      let d' : DomainRO_split := (secrets, salt, info) in
      r <--$ OC_Query _ d'; 
      $ret (cca_or_ro r, tt)
    | cca_oq_dec resp => 
      if (resp ?= R) then ($ret (cca_or_dec None, tt)) else
      r <--$ (
      s_opt <--$$ if (eqb (snd (fst resp)) (snd (fst R))) then ret (Some nil) else (@decapsFunc _ _ _ _ _ _ _ strongKE K (snd (fst resp)));
      match s_opt with
      | None => $ret (None, tt)
      | Some s => 
        match (splitKdfInputs additionalSecretLengths (fst (snd resp)) strongKE_Pos) with
        | None => $ret (None, tt)
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  =>     
          s' <- if (eqb (snd (fst resp)) (snd (fst R))) then None else (Some s);
          q <- ((((s1, s', s2), nil)), label, (projectInfo ((Ps1 ++ (fst (fst resp)) :: Ps2), (Rs1 ++ (snd (fst resp)) :: Rs2), (snd (snd resp)))));
          k <--$ query q;
          $ret (Some k, tt)
        end
      end
      ); $ret (cca_or_dec (fst r), snd r)
    end.

   Definition CtKDF_IND_CCA_bad_7 :=
      [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
      r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
      match r_opt with
      | None => ret false
      | Some (s, R, a) =>
        p <-$ (A_KE P R) _ _ randomFunc_split nil;
        [ls, auxInfo, s_A] <-3 (fst p);
        st <- (snd p);
        match (splitKdfInputs additionalSecretLengths ls strongKE_Pos)  with
        | None => ret false
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  => 
          k <-$ rndOKM;
          p <-$ ((
          R <- ((P, R), (ls, auxInfo));
          OC_Run _ _ _ (A P R k (a, s_A)) (ccaOracle_bad_7 sk R) tt) _ _ (randomFunc rndOKM _) st);
          ret (any_dec (eqb (Some s)) (map (fun x => snd (fst (fst (fst (fst x))))) (fst (split (snd p)))))
        end
      end.

    Theorem CtKDF_IND_CCA_bad_6_le_7 : 
      Pr[CtKDF_IND_CCA_bad_6] <= Pr[CtKDF_IND_CCA_bad_7].

      unfold CtKDF_IND_CCA_bad_6, CtKDF_IND_CCA_bad_7.
      eapply comp_spec_impl_le.
      fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      fcf_skip.
      eapply (fcf_oracle_eq (fun s1 s2 => snd s1 = snd s2 /\( fst s1 = true -> (any_dec (eqb (Some b1)) (map (fun x => snd (fst (fst (fst (fst x))))) (fst (split (snd s1)))) = true)))); intuition idtac.
      unfold ccaOracle_bad_6, ccaOracle_bad_7.
      simpl in *; subst.
      splitQuery; fcf_sp.
      unfold randomFunc.
      splitOpt2; fcf_sp.
      apply arrayLookup_Some_true_impl_any_dec_true in H8.
      apply orb_prop in H9; intuition idtac.
      eqbTac.
      apply any_dec_ex in H8.
      destruct H8.
      intuition idtac; eqbTac.
      rewrite <- any_dec_map.
      eapply ex_any_dec; eauto.
      simpl.
      rewrite H11.
      apply eqb_refl.
      rewrite any_dec_cons.
      apply orb_prop in H12; intuition idtac.
      simpl in *.
      rewrite H12.
      apply orb_true_r.
      eqbTac.
      rewrite H13.
      rewrite eqb_refl.
      reflexivity.
      splitIf; fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      subst.
      unfold randomFunc.
      splitOpt2; fcf_sp.
      apply arrayLookup_Some_true_impl_any_dec_true in H12.
      apply orb_prop in H14; intuition idtac.
      rewrite <- any_dec_map.
      apply any_dec_ex in H12.
      destruct H12; intuition idtac.
      eqbTac.
      apply andb_prop in H15; intuition idtac.
      eqbTac.
      destruct (snd (fst c) ?= p).
      simpl in *. discriminate.
      eapply ex_any_dec; eauto.
      simpl.
      apply eqb_refl.
      rewrite any_dec_cons.
      apply orb_prop in H16; intuition idtac.
      simpl in *.
      rewrite H16.
      apply orb_true_r.
      apply andb_prop in H17; intuition idtac.
      eqbTac.
      destruct (snd (fst c) ?= p).
      simpl in *. discriminate.
      rewrite eqb_refl.
      reflexivity.

      simpl in *.
      fcf_sp.
      trivial.

    Qed.

    (* Implement the Ct CCA oracle using the strong KE CCA oracle *)
    Definition ccaOracle_bad_8(R : CtPublicResponse)( s : list (DomainRO_split * RangeRO))(q : CCA_OracleQuery) :  OracleComp _ _  (CCA_OracleResponse  *  list (DomainRO_split * RangeRO)) :=
    match q with
    | cca_oq_ro d => 
      [secret, salt, info] <-3 d;
      secrets <- splitSecrets secret;
      let d' : DomainRO_split := (secrets, salt, info) in
      [r, s'] <--$2$ randomFunc rndOKM _ s d'; 
      $ret (cca_or_ro r, s')
    | cca_oq_dec resp => 
      if (resp ?= R) then ($ret (cca_or_dec None, s)) else
      r <--$ (
      s_opt <--$ if (eqb (snd (fst resp)) (snd (fst R))) then $ret (Some nil) else (query (snd (fst resp)));
      match s_opt with
      | None => $ret (None, s)
      | Some secret => 
        match (splitKdfInputs additionalSecretLengths (fst (snd resp)) strongKE_Pos) with
        | None => $ret (None, s)
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  =>     
          s' <- if (eqb (snd (fst resp)) (snd (fst R))) then None else (Some secret);
          q <- ((((s1, s', s2), nil)), label, (projectInfo ((Ps1 ++ (fst (fst resp)) :: Ps2), (Rs1 ++ (snd (fst resp)) :: Rs2), (snd (snd resp)))));
          [r, s'] <--$2$ randomFunc rndOKM _ s q;
          $ret (Some r, s')
        end
      end
      ); $ret (cca_or_dec (fst r), snd r)
    end.

    Definition stripOpt_def (A : Type)(def : A)(o : option A) :=
      match o with
      | Some a => a
      | None => def
    end.

    Definition CtKDF_IND_CCA_bad_8 :=
      [sk, P] <-$2 (@keyGen _ _ _ _ _ _ _ strongKE);
      r_opt <-$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
      match r_opt with
      | None => ret false
      | Some (s, R, a) =>
        p <-$ (A_KE P R) _ _ randomFunc_split nil;
        [ls, auxInfo, s_A] <-3 (fst p);
        st <- (snd p);
        match (splitKdfInputs additionalSecretLengths ls strongKE_Pos)  with
        | None => ret false
        | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  => 
          k <-$ rndOKM;
          p <-$ ((
          OC_Run _ _ _ (A P ((P, R), (ls, auxInfo)) k (a, s_A)) (ccaOracle_bad_8 ((P, R), (ls, auxInfo))) st) _ _ (@ccaOracle _ _ _ _ _ _ _ strongKE R sk) tt);
          ret (any_dec (eqb s) (map (fun x => stripOpt_def nil (snd (fst (fst (fst (fst x)))))) (fst (split (snd (fst p))))))
        end
      end.

    Theorem CtKDF_IND_CCA_bad_7_le_8 : 
      Pr[CtKDF_IND_CCA_bad_7] <= Pr[CtKDF_IND_CCA_bad_8].

      eapply comp_spec_impl_le.
      unfold CtKDF_IND_CCA_bad_7, CtKDF_IND_CCA_bad_8.
      fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      fcf_skip.
      eapply (fcf_oracle_eq (fun s1 s2 => snd s1 = fst s2)); trivial; intuition idtac.
      unfold ccaOracle_bad_7, ccaOracle_bad_8, ccaOracle.
      simpl in *; subst.
      splitQuery; fcf_sp.
      fcf_skip.
      fcf_sp.
      splitIf; fcf_sp.
      splitIf; fcf_sp.
      splitOpt; fcf_sp.
      fcf_skip.
      fcf_sp.
      rewrite H9.
      fcf_sp.
      splitOpt; fcf_sp.
      splitOpt; fcf_sp.
      
      simpl in *; fcf_sp.
      rewrite <- any_dec_map in *.
      apply any_dec_ex in H11.
      destruct H11; intuition idtac.
      eapply ex_any_dec; eauto.
      eqbTac.
      apply eqb_leibniz.
      match goal with 
      | [H1 : Some _ = ?a |-  _ =  stripOpt_def _ ?b ] =>
        assert (a = b)
      end.
      reflexivity.
      rewrite <- H10.
      rewrite <- H12.
      reflexivity.

    Qed.

    Definition strongKE_OWCCA_A P R a :=  
      p <--$$ (A_KE P R) _ _ randomFunc_split nil;
      [ls, auxInfo, s_A] <-3 (fst p);
      st <- (snd p);
      match (splitKdfInputs additionalSecretLengths ls strongKE_Pos)  with
      | None => $ret nil
      | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  => 
        k <--$$ rndOKM;
        p <--$ ((
        R <- ((P, R), (ls, auxInfo));
        OC_Run _ _ _ (A P R k (a, s_A)) (ccaOracle_bad_8 R) st));
        $ret (map (fun x => stripOpt_def nil (snd (fst (fst (fst (fst x)))))) (fst (split (snd p))))
    end.

    Theorem CtKDF_IND_CCA_bad_8_le_OWCCA : 
      Pr[CtKDF_IND_CCA_bad_8] == (@KeyExchangeOW_CCA_List_Advantage _ _ _ _ _ _ _ strongKE strongKE_OWCCA_A).

      unfold CtKDF_IND_CCA_bad_8, KeyExchangeOW_CCA_List_Advantage, KeyExchangeOW_CCA_List_G, strongKE_OWCCA_A.
      fcf_sp.
      splitOpt.
      fcf_simp.
      fcf_inline_first.
      fcf_skip.
      simpl.
      eapply comp_spec_symm.
      eapply comp_spec_eq_trans_l.
      eapply comp_spec_left_ident.
      simpl.
      fcf_sp.
      splitOpt; fcf_sp.
      fcf_sp.
    Qed.

    Theorem CtKDF_IND_CCA : 
      (@KeyExchangeCCA_O_Advantage _ _ _ _ _ _ _ _ _ CtKE _ _ A  rndOKM rndOKM) <= 
      (@KeyExchangeOW_CCA_List_Advantage _ _ _ _ _  _ _ strongKE strongKE_OWCCA_A) +
      (@KE_CorrectnessError _ _ _ _ _ _ _ strongKE).

      unfold KeyExchangeCCA_O_Advantage.
      rewrite CtKDF_IND_CCA_G1_equiv.
      eapply leRat_trans.
      eapply ratDistance_le_trans.
      eapply CtKDF_IND_CCA_G2_close.
      rewrite <- CtKDF_IND_CCA_G2_equiv.
      eapply eqRat_impl_leRat.
      apply (@ratIdentityIndiscernables ( Pr [CtKDF_IND_CCA_G2 ] )).
      reflexivity.
      rewrite <- ratAdd_0_r.
      rewrite CtKDF_IND_CCA_bad_2_equiv.
      rewrite CtKDF_IND_CCA_bad_3_equiv.    
      eapply leRat_trans.
      eapply ratDistance_le_sum.
      apply CtKDF_IND_CCA_bad_4_close.
      eapply ratAdd_leRat_compat; try reflexivity.
      rewrite CtKDF_IND_CCA_bad_4_le_5.
      rewrite CtKDF_IND_CCA_bad_6_equiv.
      rewrite CtKDF_IND_CCA_bad_6_le_7.
      rewrite CtKDF_IND_CCA_bad_7_le_8.
      rewrite CtKDF_IND_CCA_bad_8_le_OWCCA.
      reflexivity.

    Qed.

  End CtKDF_IND_CCA_ROM.

End CtKDF_ROM_CCA.





