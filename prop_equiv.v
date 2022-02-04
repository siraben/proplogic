Require Import proplogicST.
Require Import proplogic.
Require Import List.
Import ListNotations.

Fixpoint fm_to_ST (x : fm) : PL_Formula :=
  match x with
  | Impl a b => PL_imp (fm_to_ST a) (fm_to_ST b)
  | Var x => PL_var x
  | Neg a => PL_neg (fm_to_ST a)
  end.

Fixpoint ST_to_fm (x : PL_Formula) : fm :=
  match x with
  | PL_var x => Var x
  | PL_neg x => Neg (ST_to_fm x)
  | PL_imp a b => Impl (ST_to_fm a) (ST_to_fm b)
  end.

Lemma fm_ST_iso : forall A, fm_to_ST (ST_to_fm A) = A.
Proof. induction A; simpl; try congruence. Qed.

Lemma ST_fm_iso : forall A, ST_to_fm (fm_to_ST A) = A.
Proof. induction A; simpl; try congruence. Qed.

Lemma interp_equiv :
  forall f A, PL_interpretation f (fm_to_ST A) = fm_val f A.
Proof.
  intros f A.
  generalize dependent f.
  induction A; intros f.
  - cbn. unfold PL_imp_interpretation. congruence.
  - reflexivity.
  - cbn. unfold PL_neg_interpretation. congruence.
Qed.

Lemma satisfies_single :
  forall v A, Satisfies v [A] <-> Forall (PL_models v) (map fm_to_ST [A]).
Proof.
  intros v A.
  split; intros H.
  - simpl. constructor. unfold PL_models.
    unfold Satisfies in H.
    specialize (H A ltac:(left; constructor)).
    rewrite interp_equiv. assumption.
    apply Forall_nil.
  - apply Forall_inv in H.
    unfold PL_models, Satisfies in *.
    intros.
    inversion H0; subst.
    + rewrite interp_equiv in H. assumption.
    + inversion H1.
Qed.

Lemma satisfies_weaken : forall v A S, Satisfies v (A :: S) -> Satisfies v S.
Proof.
  unfold Satisfies.
  intros v A S H A0 H0.
  specialize (H A0).
  apply H. right. assumption.
Qed.

Lemma satisfies_adjoin : forall v A S, Satisfies v S -> fm_val v A = true -> Satisfies v (A :: S).
Proof.
  unfold Satisfies.
  intros v A S H H0 A0 H1.
  destruct H1; subst; auto.
Qed.

Lemma satisfies_forall :
  forall v S, Satisfies v S <-> Forall (PL_models v) (map fm_to_ST S).
Proof.
  intros v S.
  induction S.
  - split; intros; firstorder; constructor.
  - split; intros H.
    + assert (Satisfies v [a]).
      {
        unfold Satisfies in *.
        intros A H0.
        specialize (H a ltac:(left; auto)).
        inversion H0; subst; auto.
      }
      apply satisfies_single in H0.
      constructor.
      * apply Forall_inv in H0. assumption.
      * apply satisfies_weaken in H.
        apply IHS.
        assumption.
    + apply satisfies_adjoin.
      * apply Forall_inv_tail in H.
        apply IHS in H. assumption.
      * apply Forall_inv in H.
        unfold PL_models in H.
        rewrite interp_equiv in H. assumption.
Qed.

Lemma models_equiv : forall v A, PL_models v A <-> fm_val v (ST_to_fm A) = true.
Proof.
  intros v A.
  split; intros H.
  - rewrite <- interp_equiv, fm_ST_iso. unfold PL_models in H. assumption.
  - unfold PL_models. rewrite <- interp_equiv, fm_ST_iso in H.
    assumption.
Qed.

Lemma Satisfies_PL_list_models_single :
  forall S A, PL_list_models [S] A -> Models [ST_to_fm S] (ST_to_fm A).
Proof.
  intros S A H.
  unfold Models, PL_list_models in *.
  intros v H0.
  specialize (H v).
  rewrite satisfies_forall in H0.
  simpl in H0.
  rewrite fm_ST_iso in H0.
  apply H in H0.
  apply models_equiv.
  assumption.
Qed.

Lemma Satisfies_PL_list_models_equiv :
  forall S A, PL_list_models S A <-> Models (map ST_to_fm S) (ST_to_fm A).
Proof.
  split.
  - induction S; intros.
    + unfold PL_list_models in H.
      intros v.
      specialize H with v.
      specialize (H ltac:(constructor)).
      unfold PL_models in H.
      simpl.
      intros _.
      rewrite <- interp_equiv.
      rewrite fm_ST_iso.
      assumption.
    + unfold Models.
      unfold PL_list_models in IHS.
      intros v H0.
      unfold PL_list_models in H.
      specialize (H v).
      apply models_equiv, H.
      rewrite satisfies_forall in H0.
      rewrite map_map in H0.
      rewrite map_ext with (g := id) in H0 by apply fm_ST_iso.
      rewrite map_id in H0.
      assumption.
  - induction S; intros.
    + unfold Models in H.
      unfold PL_list_models.
      intros v H0.
      specialize (H v ltac:(cbv; auto)).
      apply models_equiv.
      assumption.
    + unfold PL_list_models.
      intros v H0.
      specialize (H v).
      apply models_equiv.
      apply H.
      apply satisfies_forall.
      rewrite map_map.
      rewrite map_ext with (g := id) by apply fm_ST_iso.
      rewrite map_id.
      assumption.
Qed.
