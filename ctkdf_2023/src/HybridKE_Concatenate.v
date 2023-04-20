(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: MIT-0 *)

Set Implicit Arguments.

Require Import FCF.
Require Import KeyExchange.

Local Open Scope list_scope.

Ltac splitIf := match goal with
  | [|- context[if ?a then _ else _]] =>
    case_eq a; intros
end.

Ltac splitOpt := match goal with  
| [|- context[match ?a with | Some _ => _ | None => _ end]] =>
  case_eq a; intros
end.

Ltac distToLogic :=
  try match goal with
  | [|- evalDist _ _ == evalDist _ _ ] => eapply comp_spec_impl_eq
  end.
Ltac fcf_sp_one := simpl; fcf_inline_first; fcf_simp; try
  match goal with
  | [|- comp_spec _ (Bind ?a _) (Bind ?a _)] =>
    fcf_skip
  | [|- comp_spec _ (Ret _ _) (Ret _ _ ) ] =>
    apply comp_spec_ret; intuition idtac; simpl in *; intuition idtac; simpl in *; subst
  end.

Ltac fcf_sp := distToLogic; repeat fcf_sp_one.


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

Definition BitString := list bool.

Ltac BitString_EqDec := repeat 
  match goal with
  | [|- EqDec (prod _ _) ] => apply pair_EqDec
  | [|- EqDec (list _) ] => apply list_EqDec
  | [|- EqDec BitString ] => apply list_EqDec
  | [|- EqDec (Bvector _) ] => apply Bvector_EqDec
  | [|- EqDec (option _) ] => apply option_EqDec
  end.

(* A definition of CtKDF in which the functions get oracle access to the KDF. We can specialize this definition to produce standard model and ROM forms of CtKDF. *)
Section CtKDF.
  
  Variable Salt OKM Info : Set.
  Hypothesis OKM_EqDec : EqDec OKM.
  Hypothesis Info_EqDec : EqDec Info.
  Hypothesis Salt_EqDec : EqDec Salt.
  Variable rndOKM : nat -> Comp OKM.

  Variable PrivateKey : Set.
  Variable PublicInit : Set.
  Variable PublicResponse : Set.
  Variable Aux AuxInfo : Set.

  Hypothesis PrivateKey_EqDec : EqDec PrivateKey.
  Hypothesis PublicInit_EqDec : EqDec PublicInit.
  Hypothesis PublicResponse_EqDec : EqDec PublicResponse.
  Hypothesis Aux_EqDec : EqDec Aux.
  Hypothesis AuxInfo_EqDec : EqDec AuxInfo.


  (* projectInfo is a function that chooses some of the values from the list of public keys and ciphertexts for inclusion in the info field of the KDF *)
  (* This function will have different properties in different proofs. *)
  Variable projectInfo : (list PublicInit * list PublicResponse * AuxInfo) -> Info.
  Variable label : Salt.
  (* We model the KDF as a function that only returns strings of the correct length, so there is no length parameter. 
  For security definitions in which the adversary can query the KDF, this model corresponds with an assumption that 
  querying the KDF on different lengths will produce independent results. *)

  Definition KDF_OracleInput := (BitString * Salt * Info)%type.
  Definition ctKDF k MA MB auxInfo : OracleComp KDF_OracleInput OKM OKM :=
    let secret := flatten k in
    let kdf_context := projectInfo (MA, MB, auxInfo) in
    OC_Query _ (secret, label, kdf_context).
  
  Definition BitStringKE := (@KeyExchange PrivateKey PublicInit PublicResponse Aux BitString _ _ ).

  (* Assume we have a strong KE *)
  Variable strongKE : BitStringKE.

  (* We fix the number of KEs and the position of the strong KE. Also, the number of secret bits produced by each KE is fixed. 
  Proofs are universally quantified over these parameters, and this shows security of this construction even in circumstances
  where it is not known which KE is strong. We can view these as values chosen by the adversary at the beginning of the game.*)
  Variable strongKE_Pos : nat.
  Variable additionalSecretLengths : list nat.

  Fixpoint lengthsCorrect (ls : list BitString)(lens : list nat) :=
    match ls with
    | nil => 
      match lens with
      | nil => true
      | _ :: _ => false
      end
    | s :: ls' =>
      match lens with
      | nil => false
      | len :: lens' =>
        ((length s) ?= len) && (lengthsCorrect ls' lens')
      end
    end.


  (* For all security definitions, there is an adversary procedure that sees the public outpus of the strong KE and produces the other KE outputs. 
  This adversary procedure models a number of KEs that are under the control of the adversary. *)
  Variable A_State : Set.
  Hypothesis A_State_EqDec : EqDec A_State.
  Variable A_KE : PublicInit -> PublicResponse -> OracleComp KDF_OracleInput OKM ((list (PublicInit * PublicResponse * BitString)) * AuxInfo  * A_State).

  Definition ctKeyGen := (@keyGen _ _ _  _ _ _ _ strongKE).

  Definition splitKdfInputs (ls : list (PublicInit * PublicResponse * BitString)) (n : nat) :=
    if (negb (lengthsCorrect (snd (split ls)) additionalSecretLengths)) then None else
    ls1 <- (firstn n ls);
    ls2 <- (skipn n ls);
    Ps1 <- fst (split  (fst (split ls1)));
    Rs1 <- snd (split (fst (split ls1)));
    s1 <- snd (split ls1);
    Ps2 <- fst (split  (fst (split ls2)));
    Rs2 <- snd (split (fst (split ls2)));
    s2<- snd (split ls2);
    Some (Ps1, Rs1, s1, Ps2, Rs2, s2).

  Definition CtPublicResponse := ((PublicInit * PublicResponse) * ((list (PublicInit * PublicResponse * BitString)) * AuxInfo ))%type.

  Definition ctResponseFunc (P : PublicInit)  : OracleComp KDF_OracleInput OKM (option (OKM * CtPublicResponse * (Aux * A_State))) :=
    r_opt <--$$ (@responseFunc _ _ _ _ _ _ _ strongKE P);
    match r_opt with
    | None => $ret None
    | Some (s, R, a) => 
      [ls, auxInfo, s_A] <--$3 A_KE P R;
      match (splitKdfInputs ls strongKE_Pos) with
      | None => $ret None
      | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  =>
        k <--$ ctKDF (s1 ++ s :: s2) (Ps1 ++ P :: Ps2) (Rs1 ++ R :: Rs2) auxInfo;
        $ret (Some (k, ((P, R), (ls, auxInfo)), (a, s_A)))
      end
    end.

  Definition ctDecapsFunc (K : PrivateKey)(R : CtPublicResponse) :=
    s_opt <--$$ (@decapsFunc _ _ _ _ _ _ _ strongKE K (snd (fst R)));
    match s_opt with
    | None => $ret None
    | Some s => 
      match (splitKdfInputs (fst (snd R)) strongKE_Pos) with
      | None => $ret None
      | Some (Ps1, Rs1, s1, Ps2, Rs2, s2)  =>
        k <--$ ctKDF (s1 ++ s :: s2) (Ps1 ++ (fst (fst R)) :: Ps2) (Rs1 ++ (snd (fst R)) :: Rs2) (snd (snd R));
        $ret (Some k)
      end
    end.

End CtKDF.