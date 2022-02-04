(* proplogicST.v - ver 0.1 - Steven Tschantz - 2/3/22*)
(* Laguage, sematics, and proofs for proposition logic *)
(* Lukasiewicz axiom system with countably many variables *)
(* PL = Propositional Logic *)

Require Import List.
Require Import Arith.



Section PL_options.

(* Index variables by nat.  Or switch? *)

Definition PL_VarIndex : Type := nat.

Theorem PL_decidableVarIndex : forall {x y : PL_VarIndex}, {x = y} + {~ x = y}.
Proof.
decide equality.
Qed.

Definition PL_varO := O.

Definition PL_varS := S.

Definition PL_varle := le.

Definition PL_varlt := lt.

Definition PL_varmax := max.

(* Take valuations in type bool.  For now? *)

Definition PL_Value : Type := bool.

Definition PL_neg_interpretation (b : PL_Value) : PL_Value :=  negb b.

Definition PL_imp_interpretation (b c : PL_Value) : PL_Value := orb (negb b) c.

Definition PL_top_interpretation : PL_Value := true.

Definition PL_bot_interpretation : PL_Value := false.

End PL_options.



Section PL_language.

(* We give an inductive definition of formulas *)
Inductive PL_Formula: Type :=
| PL_var : PL_VarIndex->PL_Formula
| PL_neg : PL_Formula->PL_Formula
| PL_imp : PL_Formula->PL_Formula->PL_Formula
.

Definition PL_and (A B : PL_Formula) : PL_Formula :=
PL_neg (PL_imp A (PL_neg B)).

Definition PL_or (A B : PL_Formula) : PL_Formula :=
PL_imp (PL_neg A) B.

Definition PL_iff (A B : PL_Formula) : PL_Formula :=
PL_and (PL_imp A B) (PL_imp B A).

Definition PL_top : PL_Formula := PL_imp (PL_var 0) (PL_var 0).

Definition PL_bot : PL_Formula := PL_neg PL_top.

Definition PL_listor (S : list PL_Formula) : PL_Formula :=
  fold_right PL_or PL_bot S.

Definition PL_listand (S : list PL_Formula) : PL_Formula :=
  fold_right PL_and PL_top S.

Definition PL_decidableFormula (A B : PL_Formula) : {A = B} + {~ A = B}.
Proof.
decide equality.
apply PL_decidableVarIndex.
Defined.

Definition PL_SubstFunction : Type := PL_VarIndex -> PL_Formula.

Fixpoint PL_subst (s : PL_SubstFunction) (A : PL_Formula) : PL_Formula :=
match A with
| PL_var n => s n
| PL_neg X => PL_neg (PL_subst s X)
| PL_imp X Y => PL_imp (PL_subst s X) (PL_subst s Y)
end.

Definition PL_subst1 (A : PL_Formula) : PL_SubstFunction :=
fun (n : nat) => 
match n with 
| O => A
| _ => PL_var n
end.

Definition PL_subst2 (A B : PL_Formula) : PL_SubstFunction :=
fun (n : nat) => 
match n with 
| O => A
| 1 => B
| _ => PL_var n
end.

Definition PL_subst3 (A B C : PL_Formula) : PL_SubstFunction :=
fun (n : nat) => 
match n with 
| O => A
| 1 => B
| 2 => C
| _ => PL_var n
end.

Definition PL_subst_compose (s t : PL_SubstFunction) : PL_SubstFunction :=
fun (n : PL_VarIndex) => PL_subst s (t n).

Theorem PL_subst_subst :
forall (s t : PL_SubstFunction) (A : PL_Formula),
  PL_subst (PL_subst_compose s t) A = PL_subst s (PL_subst t A).
Proof.
intros s t A.
induction A as [n | A H1 | A H2 B H3].
reflexivity.
simpl.
rewrite H1.
reflexivity.
simpl.
rewrite H2.
rewrite H3.
reflexivity.
Qed.

(* Important formulas as examples *)

Definition PL_axiom1prototype : PL_Formula :=
(PL_imp (PL_var 0) (PL_imp (PL_var 1) (PL_var 0))).

Definition PL_axiom2prototype : PL_Formula :=
PL_imp
 (PL_imp (PL_var 0) (PL_imp (PL_var 1) (PL_var 2)))
 (PL_imp (PL_imp (PL_var 0) (PL_var 1)) (PL_imp (PL_var 0) (PL_var 2))).

Definition PL_axiom3prototype : PL_Formula :=
PL_imp 
  (PL_imp (PL_neg (PL_var 0)) (PL_neg (PL_var 1)))
  (PL_imp (PL_var 1) (PL_var 0)).

Definition PL_axiom1instance (A B : PL_Formula) : PL_Formula :=
PL_subst (PL_subst2 A B) PL_axiom1prototype.

Definition PL_axiom2instance (A B C : PL_Formula) : PL_Formula :=
PL_subst (PL_subst3 A B C) PL_axiom2prototype.

Definition PL_axiom3instance (A B : PL_Formula) : PL_Formula :=
PL_subst (PL_subst2 A B) PL_axiom3prototype.

End PL_language.



Section PL_semantics.

(* These are the "models" *)
Definition PL_Valuation : Type := PL_VarIndex -> PL_Value.

(* This is the interpretation of a formula in a "model" *)
Fixpoint PL_interpretation (f : PL_Valuation) (A : PL_Formula) : PL_Value :=
match A with
| PL_var n => f n
| PL_neg X => PL_neg_interpretation (PL_interpretation f X)
| PL_imp X Y => PL_imp_interpretation (PL_interpretation f X) (PL_interpretation f Y)
end.

(* This is then $f\models A$ *)
Definition PL_models (f : PL_Valuation) (A : PL_Formula) : Prop :=
PL_interpretation f A = PL_top_interpretation.

(* We start with only finite lists of assumptions.  We might like to generalize this. *)
(* This is when a (finite) set of formulas semantically entails a formula, $S\models A$ *)
Definition PL_list_models (S : list PL_Formula) (A : PL_Formula) : Prop :=
forall (f : PL_Valuation),
  Forall (PL_models f) S -> PL_models f A.

Theorem PL_sublist_models :
forall (S T : list PL_Formula) (A : PL_Formula),
  incl S T -> PL_list_models S A -> PL_list_models T A.
Proof.
intros S T A H1 H2 f H3.
apply H2.
apply incl_Forall with T.
assumption.
assumption.
Qed.

Definition PL_valid (A : PL_Formula) : Prop := PL_list_models nil A.

Theorem PL_valid_list_models:
forall (S : list PL_Formula) (A : PL_Formula),
  PL_valid A -> PL_list_models S A.
Proof.
intros S A.
apply PL_sublist_models.
apply incl_nil_l.
Qed.

Definition PL_valuation_subst (f : PL_Valuation) (s : PL_SubstFunction) : PL_Valuation :=
fun (n : PL_VarIndex) => PL_interpretation f (s n).

Theorem PL_interpretation_subst :
forall (f : PL_Valuation) (s : PL_SubstFunction) (A : PL_Formula),
  PL_interpretation f (PL_subst s A) = PL_interpretation (PL_valuation_subst f s) A.
Proof.
intros f s A.
induction A as [n|X H1|X H2 Y H3].
reflexivity.
simpl.
rewrite H1.
reflexivity.
simpl.
rewrite H2.
rewrite H3.
reflexivity.
Qed.

Theorem PL_models_subst :
forall (f : PL_Valuation) (s : PL_SubstFunction) (A : PL_Formula),
  PL_models f (PL_subst s A) <-> PL_models (PL_valuation_subst f s) A.
Proof.
intros f s A.
unfold PL_models.
rewrite PL_interpretation_subst.
tauto.
Qed.

Theorem PL_valid_subst_valid : 
forall (s : PL_SubstFunction) (A : PL_Formula),
  PL_valid A -> PL_valid (PL_subst s A).
Proof.
intros s A H1 f H2.
assert (H3 : PL_models (PL_valuation_subst f s) A).
apply H1.
auto.
rewrite PL_models_subst.
assumption.
Qed.

Theorem PL_axiom1prototypevalid : PL_valid PL_axiom1prototype.
Proof.
intros f H.
vm_compute.
destruct (f 0); destruct (f 1); reflexivity.
Qed.
 
Theorem PL_axiom2prototypevalid : PL_valid PL_axiom2prototype.
Proof.
intros f H.
vm_compute.
destruct (f 0); destruct (f 1); destruct (f 2); reflexivity.
Qed.
 
Theorem PL_axiom3prototypevalid : PL_valid PL_axiom3prototype.
Proof.
intros f H.
vm_compute.
destruct (f 0); destruct (f 1); reflexivity.
Qed.

Theorem PL_axiom1instancevalid : 
forall (A B : PL_Formula), PL_valid (PL_axiom1instance A B).
Proof.
intros A B.
unfold PL_axiom1instance.
apply PL_valid_subst_valid.
apply PL_axiom1prototypevalid.
Qed.

Theorem PL_axiom2instancevalid : 
forall (A B C : PL_Formula), PL_valid (PL_axiom2instance A B C).
Proof.
intros A B C.
unfold PL_axiom2instance.
apply PL_valid_subst_valid.
apply PL_axiom2prototypevalid.
Qed.

Theorem PL_axiom3instancevalid : 
forall (A B : PL_Formula), PL_valid (PL_axiom3instance A B).
Proof.
intros A B.
unfold PL_axiom3instance.
apply PL_valid_subst_valid.
apply PL_axiom3prototypevalid.
Qed.

Theorem PL_MPvalid :
forall (S : list PL_Formula) (A B : PL_Formula),
  PL_list_models S A -> PL_list_models S (PL_imp A B) -> PL_list_models S B.
Proof.
intros S A B H1 H2 f H3.
assert (H4 := H2 f H3).
revert H4.
assert (H5 := H1 f H3).
revert H5.
unfold PL_models.
simpl.
destruct (PL_interpretation f A);
destruct (PL_interpretation f B);
auto.
Qed.

End PL_semantics.



Section PL_decidable_semantics.

(* We don't acutally need arbitrary functions on all variables to decide truth. *)
(* Only finitely many variables occur in any list of formulas. *)
(* Consider then funtions that are eventually constant. *)

Fixpoint PL_formula_var_bound (b : PL_VarIndex) (A : PL_Formula) : Prop :=
match A with
| PL_var n => PL_varlt n b
| PL_neg X => PL_formula_var_bound b X
| PL_imp X Y => PL_formula_var_bound b X /\ PL_formula_var_bound b Y
end.

Definition PL_formula_list_var_bound (b : PL_VarIndex) (S : list PL_Formula) : Prop :=
Forall (PL_formula_var_bound b) S.

Theorem PL_formula_list_var_bound_nil_iff :
forall (b : PL_VarIndex), PL_formula_list_var_bound b nil <-> True.
Proof.
unfold PL_formula_list_var_bound.
intros b. split.
tauto.
intros H1.
apply Forall_nil.
Qed.

Theorem PL_formula_list_var_bound_cons_iff :
forall (b : PL_VarIndex) (S : list PL_Formula) (A : PL_Formula),
  PL_formula_list_var_bound b (A::S) <-> 
  PL_formula_var_bound b A /\ PL_formula_list_var_bound b S.
Proof.
unfold PL_formula_list_var_bound.
intros b. split.
intros H1.
split.
apply (Forall_inv H1).
apply (Forall_inv_tail H1).
intros [H2 H3].
apply Forall_cons.
assumption.
assumption.
Qed.

Fixpoint PL_formula_var_max (A : PL_Formula) : PL_VarIndex :=
match A with
| PL_var n => PL_varS n
| PL_neg X => PL_formula_var_max X
| PL_imp X Y => PL_varmax (PL_formula_var_max X) (PL_formula_var_max Y)
end.

Definition PL_formula_list_var_max (S : list PL_Formula) : PL_VarIndex :=
fold_right PL_varmax PL_varO (map PL_formula_var_max S).

Theorem PL_formula_list_var_max_nil_eq :
PL_formula_list_var_max nil = PL_varO.
Proof.
reflexivity.
Qed.

Theorem PL_formula_list_var_max_cons_eq :
forall (S : list PL_Formula) (A : PL_Formula),
  PL_formula_list_var_max (A::S) = 
  PL_varmax (PL_formula_var_max A) (PL_formula_list_var_max S).
Proof.
unfold PL_formula_list_var_max.
intros S A.
reflexivity.
Qed.

Theorem PL_formula_var_bound_monotonic :
forall (m n : PL_VarIndex) (A : PL_Formula),
  PL_varle m n -> PL_formula_var_bound m A -> PL_formula_var_bound n A.
Proof.
intros m n.
induction A as [k|X H1|X H2 Y H3].
vm_compute. intros. apply le_trans with m; assumption.
simpl. assumption.
simpl. tauto.
Qed.

Theorem PL_formula_list_var_bound_monotonic :
forall (m n : PL_VarIndex) (S : list PL_Formula),
  PL_varle m n -> PL_formula_list_var_bound m S -> PL_formula_list_var_bound n S.
Proof.
unfold PL_formula_list_var_bound.
intros m n S H1 H2. induction H2 as [|A T H3 H4 H5].
apply Forall_nil.
apply Forall_cons.
apply PL_formula_var_bound_monotonic with m.
assumption.
assumption.
assumption.
Qed.

Theorem PL_formula_var_bound_max :
forall (A : PL_Formula),
  PL_formula_var_bound (PL_formula_var_max A) A.
Proof.
induction A as [n|X H1|X H2 Y H3].
vm_compute. apply le_n.
simpl. assumption.
simpl. split.
apply PL_formula_var_bound_monotonic with (PL_formula_var_max X).
apply Nat.le_max_l. assumption.
apply PL_formula_var_bound_monotonic with (PL_formula_var_max Y).
apply Nat.le_max_r. assumption.
Qed.

Theorem PL_formula_list_var_bound_max :
forall (S : list PL_Formula),
  PL_formula_list_var_bound (PL_formula_list_var_max S) S.
Proof.
induction S as [|A T H1].
apply Forall_nil.
rewrite PL_formula_list_var_bound_cons_iff.
split.
apply PL_formula_var_bound_monotonic with (PL_formula_var_max A).
unfold PL_formula_list_var_max. simpl.
apply Nat.le_max_l.
apply PL_formula_var_bound_max.
apply PL_formula_list_var_bound_monotonic with (PL_formula_list_var_max T).
apply Nat.le_max_r.
assumption.
Qed.

Theorem PL_formula_var_max_list_var_max :
  forall (B : PL_Formula) (S : list PL_Formula),
  In B S -> le (PL_formula_var_max B) (PL_formula_list_var_max S).
Proof.
intros B S.
induction S as [|B1 S1 H1].
intros H2.
exfalso.
revert H2.
apply in_nil.
unfold PL_formula_list_var_max.
simpl fold_right. simpl In. 
intros [H3|H4].
rewrite <- H3.
apply Nat.le_max_l.
apply le_trans with (PL_formula_list_var_max S1).
apply H1.
assumption.
apply Nat.le_max_r.
Qed.

Definition PL_valuations_eq_before (b : PL_VarIndex) (f g : PL_Valuation) : Prop :=
forall (n : PL_VarIndex), PL_varlt n b -> f n = g n.

Theorem PL_interpretations_eq_before :
forall (b : PL_VarIndex) (f g : PL_Valuation) (A : PL_Formula),
  PL_valuations_eq_before b f g ->
  PL_formula_var_bound b A ->
  PL_interpretation f A = PL_interpretation g A.
Proof.
intros b f g A H1. revert A.
induction A as [n|X H2|X H3 Y H4].
simpl. apply H1.
simpl. intros H5. assert (H6 := H2 H5). 
destruct (PL_interpretation f X); destruct (PL_interpretation g X);
try (reflexivity); discriminate H6.
simpl. intros [H7 H8]. assert (H9 := H3 H7). assert (H10 := H4 H8).
destruct (PL_interpretation f X); destruct (PL_interpretation g X);
destruct (PL_interpretation f Y); destruct (PL_interpretation g Y);
try (reflexivity); try (discriminate H9); discriminate H10.
Qed.

Theorem PL_models_eq_before :
forall (b : PL_VarIndex) (f g : PL_Valuation) (A : PL_Formula),
  PL_valuations_eq_before b f g ->
  PL_formula_var_bound b A ->
  PL_models f A <-> PL_models g A.
Proof.
intros b f g A H1 H2.
unfold PL_models.
split.
intros H3.
rewrite <- (PL_interpretations_eq_before b f _ _ H1 H2).
assumption.
intros H4.
rewrite (PL_interpretations_eq_before b f _ _ H1 H2).
assumption.
Qed.

Theorem PL_models_list_eq_before :
forall (b : PL_VarIndex) (f g : PL_Valuation) (S : list PL_Formula),
  PL_valuations_eq_before b f g ->
  PL_formula_list_var_bound b S ->
  Forall (PL_models f) S <-> Forall (PL_models g) S.
Proof.
intros b f g S H1.
unfold PL_formula_list_var_bound.
do 3 rewrite Forall_forall.
unfold PL_models.
intros H2.
split.
intros H3 A H4.
rewrite <- (PL_interpretations_eq_before b f _ _ H1 (H2 A H4)).
apply H3.
assumption.
intros H5 A H6.
rewrite (PL_interpretations_eq_before b f _ _ H1 (H2 A H6)).
apply H5.
assumption.
Qed.

Definition PL_valuation_shift_down (f : PL_Valuation) : PL_Valuation :=
fun (n : PL_VarIndex) => f (S n).

Theorem PL_valuations_eq_before_S_iff :
forall (b : PL_VarIndex) (f g : PL_Valuation),
  PL_valuations_eq_before (S b) f g <->
  f PL_varO = g PL_varO /\
  PL_valuations_eq_before b (PL_valuation_shift_down f) (PL_valuation_shift_down g).
Proof.
intros b f g.
split.
intros H1.
split.
apply (H1 0).
apply le_n_S.
apply le_O_n.
intros n H2.
unfold PL_valuation_shift_down.
apply H1.
apply le_n_S.
assumption.
intros [H3 H4] n H5.
destruct n as [|n1].
apply H3.
apply H4.
apply le_S_n.
assumption.
Qed.


Definition PL_valuation_top : PL_Valuation := fun (n : PL_VarIndex) => PL_top_interpretation.

Definition PL_valuation_bot : PL_Valuation := fun (n : PL_VarIndex) => PL_bot_interpretation.

Definition PL_valuation_shift_up_top (f : PL_Valuation) : PL_Valuation :=
fun (n : PL_VarIndex) =>
  match n with
  | O => PL_top_interpretation
  | S n1 => f n1
  end.

Definition PL_valuation_shift_up_bot (f : PL_Valuation) : PL_Valuation :=
fun (n : PL_VarIndex) =>
  match n with
  | O => PL_bot_interpretation
  | S n1 => f n1
  end.

Fixpoint PL_test_valuations (n : PL_VarIndex) : list (PL_Valuation) :=
match n with
| O => PL_valuation_top :: PL_valuation_bot :: nil
| S n1 => (map PL_valuation_shift_up_top (PL_test_valuations n1)) ++ 
          (map PL_valuation_shift_up_bot (PL_test_valuations n1))
end.

(* A test
Eval compute in (map (fun (f:PL_Valuation)=>f 0 :: f 1 :: f 2 ::nil) (PL_test_valuations 2)).
*)

Lemma PL_shift_up_top_shift_down:
forall (f : PL_Valuation),
  f 0 = PL_top_interpretation ->
  forall (n : PL_VarIndex),
    f n = PL_valuation_shift_up_top (PL_valuation_shift_down f) n.
Proof.
intros f H1 n.
destruct n as [|n1].
assumption.
reflexivity.
Qed.

Lemma PL_shift_up_bot_shift_down:
forall (f : PL_Valuation),
  f 0 = PL_bot_interpretation ->
  forall (n : PL_VarIndex),
    f n = PL_valuation_shift_up_bot (PL_valuation_shift_down f) n.
Proof.
intros f H1 n.
destruct n as [|n1].
assumption.
reflexivity.
Qed.

Lemma PL_shift_back_top :
forall (b : PL_VarIndex) (f g : PL_Valuation),
  f O = PL_top_interpretation ->
  PL_valuations_eq_before b (PL_valuation_shift_down f) g ->
  PL_valuations_eq_before (S b) f (PL_valuation_shift_up_top g).
Proof.
intros b f g H1 H2 n H3.
destruct n as [|n1].
assumption.
rewrite (PL_shift_up_top_shift_down f H1).
simpl.
apply H2.
apply le_S_n.
assumption.
Qed.

Lemma PL_shift_back_bot :
forall (b : PL_VarIndex) (f g : PL_Valuation),
  f O = PL_bot_interpretation ->
  PL_valuations_eq_before b (PL_valuation_shift_down f) g ->
  PL_valuations_eq_before (S b) f (PL_valuation_shift_up_bot g).
Proof.
intros b f g H1 H2 n H3.
destruct n as [|n1].
assumption.
rewrite (PL_shift_up_bot_shift_down f H1).
simpl.
apply H2.
apply le_S_n.
assumption.
Qed.

Theorem PL_bounded_valuations_listed :
forall (b : PL_VarIndex) (f : PL_Valuation),
  exists (g : PL_Valuation), In g (PL_test_valuations b) /\ PL_valuations_eq_before b f g.
Proof.
induction b as [|b1 H1].
intros f. exists PL_valuation_top.
split.
simpl.
auto.
intros n H2.
exfalso.
apply (le_Sn_O _ H2).
intros f.
destruct (H1 (PL_valuation_shift_down f)) as [g1 [H3 H4]].
destruct (f O) eqn: H5.
exists (PL_valuation_shift_up_top g1).
split.
simpl PL_test_valuations.
apply in_or_app.
left.
apply in_map.
assumption.
rewrite PL_valuations_eq_before_S_iff.
split.
assumption.
apply H4.
exists (PL_valuation_shift_up_bot g1).
split.
simpl PL_test_valuations.
apply in_or_app.
right.
apply in_map.
assumption.
rewrite PL_valuations_eq_before_S_iff.
split.
assumption.
apply H4.
Qed.

Definition PL_list_models_b (S : list PL_Formula) (A : PL_Formula) : bool :=
forallb 
  (fun (f : PL_Valuation) => 
     PL_imp_interpretation (forallb (PL_interpretation f) S) (PL_interpretation f A))
  (PL_test_valuations (PL_varmax (PL_formula_list_var_max S) (PL_formula_var_max A))).

Definition PL_list_models_b_reflects_PL_list_models:
forall (S : list PL_Formula) (A : PL_Formula),
  PL_list_models_b S A = true <-> PL_list_models S A.
Proof.
intros S A.
set (b := PL_varmax (PL_formula_list_var_max S) (PL_formula_var_max A)).
set (test := PL_test_valuations b).
split.
intros H1 f H2.
destruct (PL_bounded_valuations_listed b f) as [g [H3 H4]].
assert (H5 : Forall (PL_models g) S).
rewrite <- (PL_models_list_eq_before b f g S).
assumption.
assumption.
unfold b.
apply PL_formula_list_var_bound_monotonic with (PL_formula_list_var_max S).
apply Nat.le_max_l.
apply PL_formula_list_var_bound_max.
rewrite Forall_forall in H5.
unfold PL_models in H5.
unfold PL_list_models_b in H1.
rewrite forallb_forall in H1.
unfold PL_models.
rewrite (PL_interpretations_eq_before b f g).
assert (H6 := H1 g H3).
destruct (PL_interpretation g A) eqn: H7; 
destruct (forallb (PL_interpretation g) S) eqn: H8;
try reflexivity; try discriminate H6.
assert (H9 := (forallb_forall (PL_interpretation g) S)).
destruct H9 as [H10 H11].
rewrite H11 in H8.
discriminate H8.
assumption.
assumption.
unfold b.
apply PL_formula_var_bound_monotonic with (PL_formula_var_max A).
apply Nat.le_max_r.
apply PL_formula_var_bound_max.
unfold PL_list_models, PL_models.
unfold PL_list_models_b.
rewrite forallb_forall.
intros H12 g H13.
destruct (forallb (PL_interpretation g) S) eqn: H14;
destruct (PL_interpretation g A) eqn: H15;
try reflexivity.
rewrite H12 in H15.
discriminate H15.
rewrite Forall_forall.
rewrite forallb_forall in H14.
assumption.
Defined.

Definition PL_list_models_decidable (S : list PL_Formula) (A : PL_Formula) :
  {PL_list_models S A} + {~ PL_list_models S A}.
Proof.
destruct (PL_list_models_b S A) eqn: H1.
left.
apply PL_list_models_b_reflects_PL_list_models.
assumption.
right.
rewrite <- PL_list_models_b_reflects_PL_list_models.
intros H2.
rewrite H2 in H1.
discriminate H1.
Defined.

Definition PL_valid_decidable (A : PL_Formula) :
  {PL_valid A} + {~ PL_valid A}.
Proof.
apply PL_list_models_decidable.
Defined.

End PL_decidable_semantics.


Section PL_proofs.

Inductive PL_list_proof (S : list PL_Formula) : PL_Formula -> Type :=
| PL_assumption : forall (A : PL_Formula), In A S -> PL_list_proof S A
| PL_axiom1 : forall (A B : PL_Formula), PL_list_proof S (PL_axiom1instance A B)
| PL_axiom2 : forall (A B C : PL_Formula), PL_list_proof S (PL_axiom2instance A B C)
| PL_axiom3 : forall (A B : PL_Formula), PL_list_proof S (PL_axiom3instance A B)
| PL_MP : forall (A B : PL_Formula), 
    PL_list_proof S A -> PL_list_proof S (PL_imp A B) -> PL_list_proof S B
.

Definition PL_list_proves (S : list PL_Formula) (A : PL_Formula) :=
  inhabited (PL_list_proof S A).

Definition PL_list_proof_weaken (S T : list PL_Formula)
  (subsetST : forall (X : PL_Formula), In X S -> In X T) (A : PL_Formula) 
  (p : PL_list_proof S A) : PL_list_proof T A.
Proof.
induction p as [A0 H1|A1 B1|A2 B2 C2|A3 B3|A4 B4 H2 H3 H4 H5].
apply PL_assumption.
apply subsetST.
assumption.
apply PL_axiom1.
apply PL_axiom2.
apply PL_axiom3.
apply (PL_MP _ A4).
assumption.
assumption.
Qed.

Definition PL_subst_proof (s : PL_SubstFunction) (S : list PL_Formula) (A : PL_Formula)
  (p : PL_list_proof S A) : PL_list_proof (map (PL_subst s) S) (PL_subst s A).
Proof.
induction p as [A0 H1|A1 B1|A2 B2 C2|A3 B3|A4 B4 H2 H3 H4 H5].
apply PL_assumption.
apply in_map_iff.
exists A0.
split.
reflexivity.
assumption.
unfold PL_axiom1instance.
rewrite <- PL_subst_subst.
apply PL_axiom1.
unfold PL_axiom2instance.
rewrite <- PL_subst_subst.
apply PL_axiom2.
unfold PL_axiom3instance.
rewrite <- PL_subst_subst.
apply PL_axiom3.
apply (PL_MP _ (PL_subst s A4)).
assumption.
assumption.
Defined.

Definition PL_lemma1 : PL_Formula := PL_imp (PL_var 0) (PL_var 0).

Definition PL_lemma1_proof : PL_list_proof nil PL_lemma1.
Proof.
apply (PL_MP _ (PL_subst (PL_subst2 (PL_var 0) (PL_var 0)) PL_axiom1prototype)).
apply PL_axiom1.
apply (PL_MP _ (PL_subst (PL_subst2 (PL_var 0) PL_lemma1) PL_axiom1prototype)).
apply PL_axiom1.
apply PL_axiom2.
Defined.

Definition PL_deduction_thm_forward_proof (S : list PL_Formula) (A B : PL_Formula)
  (p : PL_list_proof S (PL_imp A B)) : PL_list_proof (A :: S) B.
Proof.
apply (PL_MP _ A).
apply PL_assumption.
apply in_eq.
apply (PL_list_proof_weaken S).
intros X.
apply in_cons.
assumption.
Defined.

Definition PL_deduction_thm_reverse_proof (S : list PL_Formula) (A B : PL_Formula)
  (p : PL_list_proof (A :: S) B) : PL_list_proof S (PL_imp A B).
Proof.
induction p as [A0 H1|A1 B1|A2 B2 C2|A3 B3|A4 B4 H2 H3 H4 H5].
destruct (PL_decidableFormula A A0) as [H6|H7].
rewrite H6.
apply (PL_list_proof_weaken nil).
intros X H8.
exfalso.
revert H8.
apply in_nil.
apply (PL_subst_proof (PL_subst1 A0) _ _ PL_lemma1_proof).
apply (PL_MP S A0).
apply PL_assumption.
destruct H1 as [H1a|H1b].
contradiction H7.
assumption.
apply (PL_axiom1 S A0 A).
apply (PL_MP _ (PL_axiom1instance A1 B1)).
apply PL_axiom1.
apply PL_axiom1.
apply (PL_MP _ (PL_axiom2instance A2 B2 C2)).
apply PL_axiom2.
apply PL_axiom1.
apply (PL_MP _ (PL_axiom3instance A3 B3)).
apply PL_axiom3.
apply PL_axiom1.
apply (PL_MP _ (PL_imp A A4)).
assumption.
apply (PL_MP _ (PL_imp A (PL_imp A4 B4))).
assumption.
apply PL_axiom2.
Defined.

Theorem PL_deduction_thm :
forall (S : list PL_Formula) (A B : PL_Formula),
  PL_list_proves S (PL_imp A B) <-> PL_list_proves (A :: S) B.
Proof.
intros S A B.
split.
intros H1.
destruct H1 as [p1].
exists.
apply PL_deduction_thm_forward_proof.
assumption.
intros H2.
destruct H2 as [p2].
exists.
apply PL_deduction_thm_reverse_proof.
assumption.
Qed.


Definition PL_lemma2 : PL_Formula := 
  PL_imp (PL_neg (PL_var 0)) (PL_imp (PL_var 0) (PL_var 1)).

Definition PL_lemma2_proof : PL_list_proof nil PL_lemma2.
Proof.
apply PL_deduction_thm_reverse_proof.
apply (PL_MP _ (PL_imp (PL_neg (PL_var 1)) (PL_neg (PL_var 0)))).
apply (PL_MP _ (PL_neg (PL_var 0))).
apply PL_assumption.
apply in_eq.
apply PL_axiom1.
apply PL_axiom3.
Defined.


Definition PL_lemma3 : PL_Formula := PL_imp (PL_neg (PL_neg (PL_var 0))) (PL_var 0).

Definition PL_lemma3_proof : PL_list_proof nil PL_lemma3.
Proof.
apply PL_deduction_thm_reverse_proof.
apply (PL_MP _ (PL_neg (PL_neg (PL_var 0)))).
apply PL_assumption.
apply in_eq.
apply (PL_MP _ (PL_imp (PL_neg (PL_var 0)) (PL_neg (PL_neg (PL_neg (PL_var 0)))))).
apply (PL_MP _ (PL_imp (PL_neg (PL_neg (PL_neg (PL_neg (PL_var 0))))) 
  (PL_neg (PL_neg (PL_var 0))))).
apply (PL_MP _ (PL_neg (PL_neg (PL_var 0)))).
apply PL_assumption.
apply in_eq.
apply PL_axiom1.
apply PL_axiom3.
apply PL_axiom3.
Defined.

Definition PL_lemma4 : PL_Formula := PL_imp (PL_var 0) (PL_neg (PL_neg (PL_var 0))).

Definition PL_lemma4_proof : PL_list_proof nil PL_lemma4.
Proof.
apply (PL_MP _ (PL_imp (PL_neg (PL_neg (PL_neg (PL_var 0)))) (PL_neg (PL_var 0)))).
apply (PL_subst_proof (PL_subst1 (PL_neg (PL_var 0))) _ _ PL_lemma3_proof).
apply PL_axiom3.
Defined.

Definition PL_lemma5 : PL_Formula := 
  PL_imp (PL_imp (PL_var 0) (PL_var 1)) (PL_imp (PL_neg (PL_var 1)) (PL_neg (PL_var 0))).

Definition PL_lemma5_proof : PL_list_proof nil PL_lemma5.
Proof.
apply PL_deduction_thm_reverse_proof.
apply (PL_MP _ (PL_imp (PL_neg (PL_neg (PL_var 0))) (PL_neg (PL_neg (PL_var 1))))).
apply PL_deduction_thm_reverse_proof.
apply (PL_MP _ (PL_var 1)).
apply (PL_MP _ (PL_var 0)).
apply (PL_MP _ (PL_neg (PL_neg (PL_var 0)))).
apply PL_assumption.
apply in_eq.
apply PL_list_proof_weaken with nil.
intros X H1.
exfalso.
revert H1.
apply in_nil.
apply PL_lemma3_proof.
apply PL_assumption.
apply in_cons.
apply in_eq.
apply PL_list_proof_weaken with nil.
intros X H1.
exfalso.
revert H1.
apply in_nil.
apply (PL_subst_proof (PL_subst1 (PL_var 1)) _ _ PL_lemma4_proof).
apply PL_axiom3.
Defined.

Definition PL_lemma6 : PL_Formula := 
  PL_imp (PL_var 0) (PL_imp (PL_neg (PL_var 1)) (PL_neg (PL_imp (PL_var 0) (PL_var 1)))).

Definition PL_lemma6_proof : PL_list_proof nil PL_lemma6.
Proof.
apply PL_deduction_thm_reverse_proof.
apply (PL_MP _ (PL_imp (PL_imp (PL_var 0) (PL_var 1)) (PL_var 1))).
apply PL_deduction_thm_reverse_proof.
apply (PL_MP _ (PL_var 0)).
apply PL_assumption.
apply in_cons.
apply in_eq.
apply PL_assumption.
apply in_eq.
apply PL_list_proof_weaken with nil.
intros X H1.
exfalso.
revert H1.
apply in_nil.
apply (PL_subst_proof (PL_subst2 _ _) _ _ PL_lemma5_proof).
Defined.

Definition PL_lemma7 : PL_Formula :=
  PL_imp (PL_imp (PL_neg (PL_var 0)) (PL_var 0)) (PL_var 0).

Definition PL_lemma7_proof : PL_list_proof nil PL_lemma7.
Proof.
apply (PL_MP _ 
  (PL_imp (PL_neg (PL_var 0)) (PL_neg (PL_imp (PL_neg (PL_var 0)) (PL_var 0))))).
apply PL_deduction_thm_reverse_proof.
apply PL_list_proof_weaken with ((PL_neg (PL_var 0))::(PL_neg (PL_var 0))::nil).
intros X H1.
destruct (in_inv H1) as [H2|H3].
rewrite <- H2.
apply in_eq.
destruct (in_inv H3) as [H4|H5].
rewrite <- H4.
apply in_eq.
exfalso.
revert H5.
apply in_nil.
apply PL_deduction_thm_forward_proof.
apply (PL_MP _ (PL_imp (PL_imp (PL_neg (PL_var 0)) (PL_var 0)) (PL_var 0))).
apply PL_deduction_thm_reverse_proof.
apply (PL_MP _ (PL_neg (PL_var 0))).
apply PL_assumption.
apply in_cons.
apply in_eq.
apply PL_assumption.
apply in_eq.
apply PL_list_proof_weaken with nil.
intros X H6.
exfalso.
revert H6.
apply in_nil.
apply (PL_subst_proof (PL_subst2 _ _) _ _ PL_lemma5_proof).
apply PL_axiom3.
Defined.

Definition PL_lemma8 : PL_Formula := 
  PL_imp (PL_imp (PL_neg (PL_var 1)) (PL_var 0)) 
    (PL_imp (PL_imp (PL_var 1) (PL_var 0)) (PL_var 0)).

Definition PL_lemma8_proof : PL_list_proof nil PL_lemma8.
Proof.
apply PL_deduction_thm_reverse_proof.
apply PL_deduction_thm_reverse_proof.
apply (PL_MP _ (PL_imp (PL_neg (PL_var 0)) (PL_neg (PL_var 1)))).
apply (PL_MP _ (PL_imp (PL_var 1) (PL_var 0))).
apply PL_assumption.
apply in_eq.
apply PL_list_proof_weaken with nil.
intros X H1.
exfalso.
revert H1.
apply in_nil.
apply (PL_subst_proof (PL_subst2 _ _) _ _ PL_lemma5_proof).
apply PL_deduction_thm_reverse_proof.
apply (PL_MP _ (PL_imp (PL_neg (PL_var 0)) (PL_var 0))).
apply PL_deduction_thm_reverse_proof.
apply (PL_MP _ (PL_neg (PL_var 1))).
apply (PL_MP _ (PL_neg (PL_var 0))).
apply PL_assumption.
apply in_eq.
apply PL_assumption.
apply in_cons.
apply in_eq.
apply PL_assumption.
apply in_cons.
apply in_cons.
apply in_cons.
apply in_eq.
apply PL_list_proof_weaken with nil.
intros X H2.
exfalso.
revert H2.
apply in_nil.
apply PL_lemma7_proof.
Defined.

End PL_proofs.



Section PL_soundness.

Theorem PL_soundness :
forall (S : list PL_Formula) (A : PL_Formula),
  PL_list_proves S A -> PL_list_models S A.
Proof.
intros S A H1.
destruct H1 as [P1].
intros f H2.
induction P1 as [A H3|A B|A B C|A B|A B PA H4 PAB H5].
rewrite Forall_forall in H2.
apply H2.
assumption.
apply PL_axiom1instancevalid.
apply Forall_nil.
apply PL_axiom2instancevalid.
apply Forall_nil.
apply PL_axiom3instancevalid.
apply Forall_nil.
unfold PL_models in H4,H5|-*.
simpl in H5.
destruct (PL_interpretation f A); destruct (PL_interpretation f B);
try reflexivity; try (discriminate H4); discriminate H5.
Qed.

End PL_soundness.


Section PL_completeness.

Definition PL_one_case_proof (f : PL_Valuation) (b : PL_VarIndex) (S : list PL_Formula) 
  (varvalues : forall (n : PL_VarIndex), PL_varlt n b ->
     (f n = true -> In (PL_var n) S) /\ (f n = false -> In (PL_neg (PL_var n)) S))
  (A : PL_Formula) (varbound : PL_varle (PL_formula_var_max A) b) :
  if (PL_interpretation f A) then (PL_list_proof S A) else (PL_list_proof S (PL_neg A)).
Proof.
revert varbound.
induction A as [n1|A H1|A H2 B H3].
intros varbound.
destruct (PL_interpretation f (PL_var n1)) eqn: H4.
apply PL_assumption.
apply varvalues.
apply Nat.lt_le_trans with (PL_formula_var_max (PL_var n1)).
apply le_n.
assumption.
assumption.
apply PL_assumption.
apply varvalues.
apply Nat.lt_le_trans with (PL_formula_var_max (PL_var n1)).
apply le_n.
assumption.
assumption.
intros varbound.
simpl.
destruct (PL_interpretation f A) eqn: H5.
apply (PL_MP _ A).
apply H1.
assumption.
apply PL_list_proof_weaken with nil.
intros X H6.
exfalso.
revert H6.
apply in_nil.
apply (PL_subst_proof (PL_subst1 A) _ _ PL_lemma4_proof).
apply H1.
assumption.
simpl.
intros H7.
simpl.
destruct (PL_interpretation f A) eqn: H8.
destruct (PL_interpretation f B) eqn: H9.
simpl.
apply (PL_MP _ B).
apply H3.
apply le_trans with (PL_varmax (PL_formula_var_max A) (PL_formula_var_max B)).
apply Nat.le_max_r.
assumption.
apply PL_axiom1.
apply (PL_MP _ (PL_neg B)).
apply H3.
apply le_trans with (PL_varmax (PL_formula_var_max A) (PL_formula_var_max B)).
apply Nat.le_max_r.
assumption.
apply (PL_MP _ A).
apply H2.
apply le_trans with (PL_varmax (PL_formula_var_max A) (PL_formula_var_max B)).
apply Nat.le_max_l.
assumption.
apply PL_list_proof_weaken with nil.
intros X H10.
exfalso.
revert H10.
apply in_nil.
apply (PL_subst_proof (PL_subst2 A B) _ _ PL_lemma6_proof).
simpl.
apply (PL_MP _ (PL_neg A)).
apply H2.
apply le_trans with (PL_varmax (PL_formula_var_max A) (PL_formula_var_max B)).
apply Nat.le_max_l.
assumption.
apply PL_list_proof_weaken with nil.
intros X H11.
exfalso.
revert H11.
apply in_nil.
apply (PL_subst_proof (PL_subst2 A B) _ _ PL_lemma2_proof).
Defined.

Definition PL_merge_case_proof (S : list PL_Formula) (A B : PL_Formula)
  (p1 : PL_list_proof (B :: S) A) (p2 : PL_list_proof ((PL_neg B) :: S) A) :
  PL_list_proof S A.
Proof.
apply (PL_MP _ (PL_imp B A)).
apply PL_deduction_thm_reverse_proof.
assumption.
apply (PL_MP _ (PL_imp (PL_neg B) A)).
apply PL_deduction_thm_reverse_proof.
assumption.
apply PL_list_proof_weaken with nil.
intros X H1.
exfalso.
revert H1.
apply in_nil.
apply (PL_subst_proof (PL_subst2 _ _) _ _ PL_lemma8_proof).
Defined.

Definition PL_valuation_k_to_top (k : PL_VarIndex) (f : PL_Valuation) : PL_Valuation :=
fun (n : PL_VarIndex) =>
match eq_nat_dec k n with
| left _ => PL_top_interpretation
| right _ => f n
end.

Definition PL_valuation_k_to_bot (k : PL_VarIndex) (f : PL_Valuation) : PL_Valuation :=
fun (n : PL_VarIndex) =>
match eq_nat_dec k n with
| left _ => PL_bot_interpretation
| right _ => f n
end.

Fixpoint PL_test_valuations2 (b : PL_VarIndex) : list PL_Valuation :=
match b with
| O => PL_valuation_bot :: nil
| S b1 => concat
  (map 
    (fun (f : PL_Valuation) => 
      (PL_valuation_k_to_top b1 f) :: (PL_valuation_k_to_bot b1 f) :: nil) 
     (PL_test_valuations2 b1))
end.

Theorem PL_bounded_valuations2_listed :
forall (b : PL_VarIndex) (f : PL_Valuation),
  exists (g : PL_Valuation), In g (PL_test_valuations2 b) /\ PL_valuations_eq_before b f g.
Proof.
induction b as [|b1 H1].
intros f.
exists PL_valuation_bot.
split.
apply in_eq.
intros n H2.
exfalso.
revert H2.
apply le_Sn_0.
intros f.
destruct (H1 f) as [g1 [H3 H4]].
destruct (f b1) eqn: H5.
exists (PL_valuation_k_to_top b1 g1).
split.
apply in_concat.
exists ((PL_valuation_k_to_top b1 g1) :: (PL_valuation_k_to_bot b1 g1) :: nil).
split.
apply in_map_iff.
exists g1.
split.
reflexivity.
assumption.
apply in_eq.
intros n H6.
unfold PL_valuation_k_to_top.
destruct (eq_nat_dec b1 n) as [H7|H8].
rewrite <- H7.
assumption.
apply H4.
unfold PL_varlt, lt in H6.
rewrite Nat.le_lteq in H6.
destruct H6 as [H9|H10].
apply le_S_n.
assumption.
exfalso.
apply H8.
inversion H10 as [H11].
reflexivity.
exists (PL_valuation_k_to_bot b1 g1).
split.
apply in_concat.
exists ((PL_valuation_k_to_top b1 g1) :: (PL_valuation_k_to_bot b1 g1) :: nil).
split.
apply in_map_iff.
exists g1.
split.
reflexivity.
assumption.
apply in_cons.
apply in_eq.
intros n H6.
unfold PL_valuation_k_to_bot.
destruct (eq_nat_dec b1 n) as [H7|H8].
rewrite <- H7.
assumption.
apply H4.
unfold PL_varlt, lt in H6.
rewrite Nat.le_lteq in H6.
destruct H6 as [H9|H10].
apply le_S_n.
assumption.
exfalso.
apply H8.
inversion H10 as [H11].
reflexivity.
Qed.

Fixpoint PL_prepend_var_for_valuation 
  (k : PL_VarIndex) (f : PL_Valuation) (S : list PL_Formula) : list PL_Formula :=
match k with
| O => S
| S k1 => (if (f k1) then (PL_var k1) else (PL_neg (PL_var k1))) :: 
  (PL_prepend_var_for_valuation k1 f S)
end.

Fixpoint PL_completeness_lemma_prod_type 
  (k : PL_VarIndex) (S : list PL_Formula) (A : PL_Formula) (F : list PL_Valuation) : Type :=
match F with
| nil => True
| f1 :: F1 => PL_list_proof (PL_prepend_var_for_valuation k f1 S) A * 
  PL_completeness_lemma_prod_type k S A F1
end.

Definition PL_models_lemma (f : PL_Valuation) (S : list PL_Formula) (A : PL_Formula)
  (H : PL_list_models S A) : 
  {B : PL_Formula & In B S /\ PL_interpretation f B = false} + 
  (PL_interpretation f A = true).
Proof.
assert (Hf := H f).
clear H.
induction S as [|B1 S1 H1].
right.
apply Hf.
apply Forall_nil.
destruct (PL_interpretation f B1) eqn: H2.
assert (H3 : Forall (PL_models f) S1 -> PL_models f A).
intros H3.
apply Hf.
apply Forall_cons.
assumption.
assumption.
destruct (H1 H3) as [[B2 [H4 H5]]|H6].
left.
exists B2.
split.
apply in_cons.
assumption.
assumption.
right.
assumption.
left.
exists B1.
split.
apply in_eq.
assumption.
Defined.

Theorem PL_prepend_var_for_valuation_lemma2 :
forall (f : PL_Valuation) (B : PL_Formula) (S : list PL_Formula),
  In B S -> forall (k : PL_VarIndex), In B (PL_prepend_var_for_valuation k f S).
Proof.
intros f B S H k.
induction k as [|k1 H1].
assumption.
apply in_cons.
assumption.
Qed.

Theorem PL_prepend_var_for_valuation_lemma3 :
  forall (f : PL_Valuation) (S : list PL_Formula) (b n : PL_VarIndex),
    PL_varlt n b ->
    (f n = true -> In (PL_var n) (PL_prepend_var_for_valuation b f S)) /\ 
    (f n = false -> In (PL_neg (PL_var n)) (PL_prepend_var_for_valuation b f S)).
Proof.
intros f S b.
induction b as [|b1 H1].
intros n H1.
exfalso.
revert H1.
apply le_Sn_0.
intros n H2.
unfold PL_varlt, lt in H2.
rewrite Nat.le_lteq in H2.
destruct H2 as [H3|H4].
assert (H5 : n < b1).
apply le_S_n.
assumption.
destruct (H1 n H5) as [H6 H7].
destruct (f n) eqn: H8.
split.
intros H9.
apply in_cons.
apply H6.
assumption.
intros H10.
apply in_cons.
apply H7.
assumption.
split.
intros H9.
apply in_cons.
apply H6.
assumption.
intros H10.
apply in_cons.
apply H7.
assumption.
rewrite <- H4.
simpl PL_prepend_var_for_valuation.
destruct (f n) eqn: H11.
split.
intros H12.
apply in_eq.
intros H13.
discriminate H13.
split.
intros H14.
discriminate H14.
intros H15.
apply in_eq.
Qed.

Definition PL_completeness_lemma1 (S : list PL_Formula) (A : PL_Formula)
  (H : PL_list_models S A) (F : list PL_Valuation) :
  PL_completeness_lemma_prod_type (max (PL_formula_list_var_max S) (PL_formula_var_max A)) 
    S A F.
Proof.
induction F as [|f1 F1 H1].
exact I.
split.
destruct (PL_models_lemma f1 _ _ H) as [[B1 [H2 H3]]|H4].
assert (H5 := PL_one_case_proof f1 
  (Init.Nat.max (PL_formula_list_var_max S) (PL_formula_var_max A))
  (PL_prepend_var_for_valuation
     (Init.Nat.max (PL_formula_list_var_max S) (PL_formula_var_max A)) f1 S)
  (PL_prepend_var_for_valuation_lemma3 f1 S _)
  B1
  ).
rewrite H3 in H5.
apply (PL_MP _ B1).
apply PL_assumption.
apply PL_prepend_var_for_valuation_lemma2.
assumption.
apply (PL_MP _ (PL_neg B1)).
apply H5.
apply le_trans with (PL_formula_list_var_max S).
apply PL_formula_var_max_list_var_max.
assumption.
apply Nat.le_max_l.
apply PL_list_proof_weaken with nil.
intros X H6.
exfalso.
revert H6.
apply in_nil.
apply (PL_subst_proof (PL_subst2 _ _) _ _ PL_lemma2_proof).
assert (H7 := PL_one_case_proof f1 
  (Init.Nat.max (PL_formula_list_var_max S) (PL_formula_var_max A))
  (PL_prepend_var_for_valuation
     (Init.Nat.max (PL_formula_list_var_max S) (PL_formula_var_max A)) f1 S)
  (PL_prepend_var_for_valuation_lemma3 f1 S _)
  A
  ).
rewrite H4 in H7.
apply H7.
apply Nat.le_max_r.
assumption.
Defined.

Theorem PL_prepend_var_for_valuation_lemma4 :
forall (v : PL_Value) (f : PL_Valuation) (S : list PL_Formula) (k m : PL_VarIndex),
  le k m ->
  PL_prepend_var_for_valuation k
    (fun (n : PL_VarIndex) => if Nat.eq_dec m n then v else f n) S =
  PL_prepend_var_for_valuation k f S.
Proof.
intros v f S k.
induction k as [|k1 H1].
intros m H2.
reflexivity.
intros m H3.
simpl.
destruct (Nat.eq_dec m k1) as [H4|H5].
exfalso.
revert H3.
rewrite H4.
apply le_Sn_n.
rewrite H1.
reflexivity.
apply le_trans with (Datatypes.S k1).
apply le_n_Sn.
assumption.
Defined.

Definition PL_completeness_lemma2 (k : PL_VarIndex) (S : list PL_Formula) (A : PL_Formula) 
  (F : list PL_Valuation)
  (p : PL_completeness_lemma_prod_type (Datatypes.S k) S A
    (concat (map 
      (fun (f : PL_Valuation) => 
        (PL_valuation_k_to_top k f) :: (PL_valuation_k_to_bot k f) :: nil) 
      F))) :
  PL_completeness_lemma_prod_type k S A F.
Proof.
induction F as [|f1 F1 p1].
exact I.
split.
assert (p2 := fst p).
assert (p3 := fst (snd p)).
simpl in p2, p3.
unfold PL_valuation_k_to_top in p2.
unfold PL_valuation_k_to_bot in p3.
destruct (Nat.eq_dec k k) as [H1|H2].
simpl in p2, p3.
rewrite PL_prepend_var_for_valuation_lemma4 in p2.
rewrite PL_prepend_var_for_valuation_lemma4 in p3.
apply (PL_merge_case_proof _ _ _ p2 p3).
apply le_n.
apply le_n.
exfalso.
apply H2.
reflexivity.
apply p1.
apply (snd (snd p)).
Defined.

Definition PL_completeness_lemma3 (S : list PL_Formula) (A : PL_Formula)
  (p : PL_completeness_lemma_prod_type 0 S A (PL_test_valuations2 0)) :
  PL_list_proof S A.
Proof.
destruct p.
assumption.
Defined.

Definition PL_completeness_proof_induction (S : list PL_Formula) (A : PL_Formula)
  (H : PL_list_models S A) (k : PL_VarIndex) :
  PL_completeness_lemma_prod_type k S A (PL_test_valuations2 k) -> PL_list_proof S A.
Proof.
induction k as [|k1 H1].
apply PL_completeness_lemma3.
intros p1.
apply H1.
apply PL_completeness_lemma2.
assumption.
Defined. 

Definition PL_completeness_proof (S : list PL_Formula) (A : PL_Formula) 
  (H : PL_list_models S A) : PL_list_proof S A.
Proof.
apply PL_completeness_proof_induction with 
  (max (PL_formula_list_var_max S) (PL_formula_var_max A)).
assumption.
apply PL_completeness_lemma1.
assumption.
Defined.

Theorem PL_completeness :
forall (S : list PL_Formula) (A : PL_Formula),
  PL_list_models S A -> PL_list_proves S A.
Proof.
intros S A H.
exists.
apply PL_completeness_proof.
assumption.
Qed.

End PL_completeness.




Section PL_decidable_proofs.

Definition PL_list_proves_decidable (S : list PL_Formula) (A : PL_Formula) :
  {PL_list_proves S A} + {~ PL_list_proves S A}.
Proof.
destruct (PL_list_models_decidable S A) as [H1|H2].
left.
apply PL_completeness.
assumption.
right.
intros H3.
apply H2.
apply PL_soundness.
assumption.
Defined.

End PL_decidable_proofs.
