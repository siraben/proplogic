Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.

Import ListNotations.
Import Nat.

Inductive fm : Type :=
| Impl (a : fm) (b : fm)
| Var (x : string)
| Neg (a : fm).

Coercion Var : string >-> fm.

Declare Custom Entry fm.
Declare Scope fm_scope.

Notation "<{ e }>" := e (at level 0, e custom fm at level 99) : fm_scope.
Notation "( x )" := x (in custom fm, x at level 99) : fm_scope.
Notation "x" := x (in custom fm at level 0, x constr at level 0) : fm_scope.
Notation "'#' x"  := (Var x) (in custom fm at level 77, right associativity).
Notation "'~' b"  := (Neg b) (in custom fm at level 75, right associativity).
Notation "x -> y" := (Impl x y) (in custom fm at level 80, right associativity).

Open Scope fm_scope.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Definition valuation := string -> bool.

Fixpoint fm_val (v : valuation) (t : fm) :=
  match t with
  | <{a -> b}> => negb (fm_val v a) || fm_val v b
  | <{# x}> => v x
  | <{~ a}> => negb (fm_val v a)
  end.

(* A valuation v satisfies Γ if all formulas in Γ are true under v. *)
Definition Satisfies v Γ := forall A, In A Γ -> fm_val v A = true.
(* Γ models a formula A if for every valuation v that satisfies Γ, A
   is true under v. *)
Definition Models Γ A := forall v, Satisfies v Γ -> fm_val v A = true.
Hint Unfold Models : core.
Notation "Γ ⊨ A" := (Models Γ A) (at level 80).
(* A is a tautology if it holds under the empty context *)
Definition Tautology A := [] ⊨ A.

(** * L system *)

(** ** Axiom schemas of L *)
Inductive AxiomL : fm -> Type :=
| A1 : forall (A B : fm),   AxiomL <{A -> B -> A}>
| A2 : forall (A B C : fm), AxiomL <{(A -> B -> C) -> (A -> B) -> (A -> C)}>
| A3 : forall (A B : fm),   AxiomL <{(~ A -> ~ B) -> (B -> A)}>.

Reserved Notation "s '|-' t" (at level 101, t custom fm at level 0).

Theorem fm_eq_dec : forall (A B : fm), {A = B} + {A <> B}.
Proof.
  intros; decide equality; apply string_dec.
Defined.

(** ** Inference rules of L *)
Inductive ltheorem (S : list fm) : fm -> Type :=
| Lassmp : forall A, existsb (fun B => if fm_eq_dec A B then true else false) S = true
             (* ---------- *)
              -> S |- A

| Lax : forall {A}, AxiomL A
          (* ---------- *)
           -> S |- A

| Lmp : forall {A B} , S |- (A -> B)
                -> S |- A
               (* ------------- *)
                -> S |- B
where "s '|-' t" := (ltheorem s t).


Fixpoint proof_size {F B} (p : ltheorem F B) : nat  :=
  match p with
  | Lassmp _ A x => 1
  | Lax _ x => 1
  | Lmp _ x x0 => 1 + proof_size x + proof_size x0
  end.

(* An axiom is valid in any context. *)
Theorem M_ax : forall A S, AxiomL A -> S ⊨ A.
Proof.
  intros A S H.
  destruct H; unfold Models; simpl; intros v Hv.
  - destruct (fm_val v A), (fm_val v B); reflexivity.
  - destruct (fm_val v A), (fm_val v B), (fm_val v C); reflexivity.
  - destruct (fm_val v A), (fm_val v B); reflexivity.
Qed.

(* Modus ponens is semantically valid *)
Theorem M_MP : forall S A B,
    S ⊨ <{A -> B}> -> S ⊨ A -> S ⊨ B.
Proof.
  intros S a b Ha Hab.
  (* Fix a valuation v *)
  intros v satV.
  specialize (Ha _ satV).
  specialize (Hab _ satV).
  simpl in *.
  now destruct (fm_val v a); destruct (fm_val v b).
Qed.

(* Proof of soundness *)
Theorem l_sound : forall S A, S |- A -> S ⊨ A.
Proof.
  intros S A H.
  induction H.
  - apply existsb_exists in e.
    destruct e.
    unfold Models.
    unfold Satisfies.
    intros v H0.
    apply H0.
    destruct (fm_eq_dec A x); subst; try easy.
  - now apply M_ax.
  - eapply M_MP; eauto.
Qed.

(* Weakening *)
Theorem weak : forall S A B, (S |- A) -> (B::S) |- A.
Proof.
  intros S A B H.
  induction H.
  - apply Lassmp. simpl.
    now destruct (fm_eq_dec A B).
  - apply Lax. assumption.
  - eapply Lmp; eauto.
Qed.

Theorem weak_l : forall S A, [] |- A -> S |- A.
Proof.
  intros S A H.
  induction S; try apply weak; auto.
Qed.

Theorem proof_size_not_0 : forall A B (F : ltheorem A B), proof_size F <> 0.
Proof.
  intros. destruct F; easy.
Qed.

(* Deduction theorem, forward direction *)
Theorem dedl : forall S A B, (S |- <{A -> B}>) -> ((A::S) |- B).
Proof.
  intros S A B.
  intros H.
  - assert (A :: S |- A).
    {
      apply Lassmp. simpl. destruct (fm_eq_dec A A); auto.
    }
    assert (A :: S |- <{A -> B}>) by now apply weak.
    eapply Lmp; eauto.
Qed.

(* Example of a tautology *)
(* Note that this matches the paper proof of A -> A for all contexts G *)
Example id_proof : forall G A, G |- <{ A -> A }>.
Proof.
  intros.
  pose proof (Lax G (A2 A <{A -> A}> A)) as L1.
  pose proof (Lax G (A1 A <{A -> A}>)) as L2.
  pose proof (Lmp G L1 L2) as L3.
  pose proof (Lax G (A1 A A)) as L4.
  pose proof (Lmp G L3 L4) as L5.
  assumption.
Defined.

Require Import Wf_nat.
Theorem strong_ind : forall P : nat -> Set,
    (forall x : nat, (forall y : nat, y < x -> P y) -> P x) -> forall a : nat, P a.
Proof.
  apply (well_founded_induction lt_wf).
Defined.

Theorem dedr0 : forall S A B (H : (A::S) |- B), proof_size H = 0 -> (S |- <{A -> B}>).
Proof.
  intros. pose proof (proof_size_not_0 _ _ H). congruence.
Qed.

Theorem dedr1 : forall G A B (H : (A::G) |- B), proof_size H = 1 -> (G |- <{A -> B}>).
Proof.
  intros.
  destruct H.
  + clear H0.
    simpl in e.
    destruct (fm_eq_dec A0 A); subst.
    * apply id_proof.
    * simpl in e.
      assert (G |- A0) by now constructor.
      pose proof (Lax G (A1 A0 A)).
      pose proof (Lmp G H0 H).
      assumption.
  + clear H0.
    simpl in a.
    assert (G |- A0) by now apply Lax.
    pose proof (Lax G (A1 A0 A)).
    pose proof (Lmp G H0 H).
    assumption.
  + simpl in H0.
    inversion H0.
    symmetry in H0.
    pose proof (proof_size_not_0 _ _ H). apply Plus.plus_is_O in H3. now destruct H3.
Defined.

Require Import Psatz.
(* Given that we have a proof H of (A::G) |- B and assuming that we can perform DT
   for proofs less than H then DT holds for H *)

(* Deduction theorem, converse direction *)
Theorem dedr : forall S A B, ((A::S) |- B) -> (S |- <{A -> B}>).
Proof.
  intros G A B H.
  remember (proof_size H) as n.
  generalize dependent H.
  generalize dependent B.
  generalize dependent A.
  generalize dependent n.
  set (P n := forall (A B : fm) (H : A :: G |- B), n = proof_size H -> G |- (A -> B)).
  change (forall n, P n).
  (* Perform strong induction on the size of the proof *)
  apply strong_ind; unfold P; clear P; intros.
  destruct x as [|[|]].
  + (* proof size = 0 *) eapply dedr0; eauto.
  + (* proof size = 1 *) eapply dedr1; eauto.
  + destruct H0; try inversion H1.
    rename A0 into C.
    assert (proof_size H0_ < S (S n)) by lia.
    assert (proof_size H0_0 < S (S n)) by lia.
    pose proof (H _ H0 _ _ H0_ eq_refl).
    pose proof (H _ H3 _ _ H0_0 eq_refl).
    pose proof (Lax G (A2 A C B)).
    pose proof (Lmp _ H6 H4).
    pose proof (Lmp _ H7 H5).
    assumption.
Defined.


(* Example proof of A -> A using the deduction theorem . *)
Example id_proof2 : forall G A, G |- <{A -> A}>.
Proof.
  intros G A.
  apply dedr.
  apply Lassmp.
  simpl; now destruct (fm_eq_dec A A).
Defined.

(* Fun example: since we're in a constructive setting, we can ask Coq
   what the derivation for X -> X is *)
Eval cbv in (id_proof [] X).
     (* = Lmp [] *)
     (*     (Lmp [] (Lax [] (A2 <{ # "X" }> <{ # "X" -> # "X" }> <{ # "X" }>)) *)
     (*        (Lax [] (A1 <{ # "X" }> <{ # "X" -> # "X" }>))) *)
     (*     (Lax [] (A1 <{ # "X" }> <{ # "X" }>)) *)
     (* : [] |- (# X -> # X) *)

(* Likewise for the second proof of X -> X using the deduction theorem. *)
Eval cbv in (id_proof2 [] X).
     (* = Lmp [] *)
     (*     (Lmp [] (Lax [] (A2 <{ # "X" }> <{ # "X" -> # "X" }> <{ # "X" }>)) *)
     (*        (Lax [] (A1 <{ # "X" }> <{ # "X" -> # "X" }>))) *)
     (*     (Lax [] (A1 <{ # "X" }> <{ # "X" }>)) *)
     (* : [] |- (# X -> # X) *)

(* In fact the proofs are equal for a concrete variable X under the
   empty context. *)
Lemma id_proofs_same : id_proof [] X = id_proof2 [] X.
Proof. reflexivity. Qed.

(* Note that they're not necessarily equal when X is an arbitrary formula or when
  the context is non-empty. *)

Lemma lemma21 : forall A B, [] |- <{(A -> (A -> B)) -> (A -> B)}>.
Proof.
  intros A B.
  apply dedr, dedr.
  assert ([A;<{A -> A -> B}>] |- A).
  {
    apply Lassmp. simpl. destruct (fm_eq_dec A A); auto.
  }
  assert ([A;<{A -> A -> B}>] |- <{A -> A -> B}>).
  {
    apply Lassmp. unfold existsb.
    destruct (fm_eq_dec _ _); destruct (fm_eq_dec _ _); auto.
  }
  pose proof (Lmp _ H0 H) as L3.
  pose proof (Lmp _ L3 H) as L4.
  assumption.
Qed.

Lemma lemma22 : forall A B, [] |- <{(A -> B) -> (A -> (A -> B))}>.
Proof.
  intros A B.
  apply dedr, dedr, weak, dedl, id_proof.
Qed.

Lemma lemma31 : forall A, [] |- <{~ ~ A -> A}>.
Proof.
  intros A.
  apply dedr.
  assert ([<{ ~ ~ A }>] |- <{~ ~ A -> A}>).
  {
    apply dedr, weak.
    remember [<{ ~ ~ A }>] as G.
    assert (G |- ~ ~ A) as L1.
    {
      rewrite HeqG.
      apply dedl, id_proof.
    }
    pose proof (Lax G (A1 <{~ ~ A}> <{~ ~ ~ ~A}>)) as L2.
    pose proof (Lmp _ L2 L1) as L3.
    pose proof (Lax G (A3 <{~ ~ ~ A}> <{~ A}>)) as L4.
    pose proof (Lmp _ L4 L3) as L5.
    pose proof (Lax G (A3 A <{~ ~ A}>)) as L6.
    pose proof (Lmp _ L6 L5) as L7.
    pose proof (Lmp _ L7 L1) as L8.
    assumption.
  }
  assert ([<{~ ~ A}>] |- <{~ ~ A}>) by apply dedl, id_proof.
  exact (Lmp _ H H0).
Qed.

Lemma lemma32 : forall A, [] |- <{A -> ~ ~ A}>.
Proof.
  intros A.
  pose proof (lemma31 <{~ A}>).
  pose proof (Lax [] (A3 <{~ ~ A}> A)).
  eapply Lmp; eauto.
Qed.

Lemma contraction : forall A B S, [A;A] ++ S |- B -> A::S |- B.
Proof.
  intros A B S H.
  apply dedr in H.
  assert (A :: S |- A).
  {
    apply Lassmp.
    simpl; now destruct (fm_eq_dec _ _).
  }
  pose proof (Lmp _ H H0).
  assumption.
Qed.


Lemma lemma4 : forall A, [] |- <{(~ A -> A) -> A}>.
Proof.
  intros A.
  assert ([<{~ A}>] |- <{(~ A -> A) -> A}>).
  {
    apply dedr.
    remember [<{ ~ A -> A }>; <{ ~ A }>] as G.
    assert (G |- <{~ A -> A}>).
    {
      apply Lassmp. rewrite HeqG. simpl.
      destruct (fm_eq_dec _ _); auto.
    }
    assert (G |- <{~ A}>).
    {
      rewrite HeqG.
      apply weak, dedl, id_proof.
    }
    exact (Lmp _ H H0).
  }
  pose proof (lemma32 A).
  pose proof (lemma31 <{~ A -> A}>).
  assert ([<{(~ A -> A) -> A}>] |- ~ ~ (~ A -> A) -> ~ ~ A).
  {
    apply dedr.
    remember [<{ ~ ~ (~ A -> A) }>; <{ (~ A -> A) -> A }>] as G.
    assert (G |- A).
    {
      subst.
      apply Lmp with <{~ A -> A}>.
      - apply Lassmp. simpl. now destruct (fm_eq_dec _ _).
      - assert ([<{ ~ ~ (~ A -> A) }>; <{ (~ A -> A) -> A }>] |- ~ ~ (~ A -> A)).
        {
          apply Lassmp. simpl. now destruct (fm_eq_dec _ _).
        }
        apply (weak_l [<{ ~ ~ (~ A -> A) }>; <{ (~ A -> A) -> A }>]) in H1.
        apply (Lmp _ H1 H2).
    }
    apply weak_l with (S := G) in H0.
    apply (Lmp _ H0 H2).
  }
  pose proof (Lax [] (A3 <{~ (~ A -> A)}> <{~ A}>)).
  assert ([<{~ A}>] |- <{~ A -> ~ (~ A -> A)}>).
  {
    apply dedr in H2.
    apply weak_l with (S := [<{ ~ A }>]) in H2.
    apply weak_l with (S := [<{ ~ A }>]) in H3.
    pose proof (Lmp _ H2 H).
    pose proof (Lmp _ H3 H4).
    assumption.
  }
  apply dedl in H4.
  assert ([<{ ~ A }>] |- (~ (~ A -> A))) by (exact (contraction _ _ _ H4)).
  pose proof (Lax [] (A3 A <{~ A -> A}>)).
  apply dedr in H5.
  pose proof (Lmp _ H6 H5).
  assumption.
Qed.

Lemma lemma5 : forall A B, [] |- <{~ A -> (A -> B)}>.
Proof.
  intros A B.
  epose proof (Lax [] (A2 _ _ _)) as L1.
  epose proof (Lax [] (A1 _ _)) as L2.
  epose proof (Lax [] (A3 _ _)) as L3.
  epose proof (Lmp [] L2 L3) as L4.
  epose proof (Lmp [] L1 L4) as L5.
  epose proof (Lax [] (A1 _ _)) as L6.
  epose proof (Lmp [] L5 L6) as L7.
  eassumption.
Qed.

(* Note: we'd like to write exists A, S |- A /\ S |- <{~A}> but we
   can't because we need to be in Set not Prop *)
Definition inconsistent (S : list fm) := {A : fm & S |- A & S |- <{~ A}>}.
Definition consistent S := inconsistent S -> False.

(* An inconsistent set proves any formula *)
Lemma inconsistent_proves_all : forall S, inconsistent S -> forall A, S |- A.
Proof.
  intros S H A.
  destruct H as [x Hx HNx].
  pose proof ((lemma5 x A)).
  apply weak_l with (S := S) in H.
  pose proof (Lmp _ H HNx).
  pose proof (Lmp _ H0 Hx).
  assumption.
Qed.

Lemma lemma6r : forall S A, S |- A -> inconsistent (<{~ A}>::S).
Proof.
  intros S A H.
  apply (weak _ _ <{~ A}>) in H.
  assert (<{~ A }> :: S |- <{~A}>) by apply dedl, id_proof.
  unfold inconsistent.
  now exists A.
Qed.

Lemma lemma6l : forall S A, inconsistent (<{~ A}>::S) -> S |- A.
Proof.
  intros S A H.
  pose proof (inconsistent_proves_all _ H A).
  assert (S |- <{~ A -> A}>) by (now apply dedr).
  pose proof (weak_l S _ (lemma4 A)).
  pose proof (Lmp _ H2 H1).
  assumption.
Qed.

Require Import Decidable.

(* A subset of a consistent set is consistent. *)
Theorem consistent_drop : forall S A, consistent (A :: S) -> consistent S.
Proof.
  intros S A H.
  unfold consistent, inconsistent in *.
  intros [x Hx HNx].
  apply H.
  exists x; apply weak; auto.
Qed.

Theorem consistent_incl : forall S P, consistent S -> incl P S -> consistent P.
Proof.
  intros S P.
  generalize dependent S.
  induction P; intros S HS HP.
  - admit.
  - unfold incl in HP.
Admitted.


Require Import Coq.Logic.ClassicalEpsilon.

(* This is classically equivalent to S ⊨ A -> S |- A. *)
Theorem l_complete : forall S A, (S ⊨ A /\ (S |- A -> False)) -> False.
Proof.
  intros S A [H1 H2].
  assert (consistent (<{~ A}> :: S)).
  {
    unfold consistent. intros contra.
    apply lemma6l in contra.
    auto.
  }
(* "Since a union of an increasing chain of consistent sets is
consistent, there must be a maximal consistent set S' containing S ∪
{¬ A}."

I'm not sure how to use axiom of choice here yet. TODO: probably
unnecessary for finite contexts

See also: Teichmuller-Tukey principle

 *)
Admitted.

