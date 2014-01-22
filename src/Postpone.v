Require Import Untyped.
Require Import Subst.
Require Import Rels.
Require Import Relation_Operators.
Require Import Relation_Definitions.
Require Import Coq.Structures.Equalities.
Require Import Coq.Program.Equality.
Require Import Beta.
Require Import Eta.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Lt.
Require Import Omega.

Module Export Postpone.

Lemma lam_k_beta_subst:
  forall k, forall M M' N N',
    beta_par M M' -> beta_par N N' ->
      beta_par (App (lam_k k (Lam M)) N) (subst 0 N' M').
Proof.
  induction k.
  (** k := 0 **)
  intros.
  simpl. apply beta_par_base; assumption.
  (** k := (S k) **)
  intros.
  simpl.
  apply beta_par_base. rewrite shift_0_lam_commute.
  unfold shift. simpl.
  replace M' with (subst 0 (Var 0) (shift 1 M')).
  apply IHk.
  apply beta_par_shift. assumption. apply beta_par_refl.
  apply subst_k_shift_S_k. assumption.
Qed.


Lemma lam_k_beta_lam:
  forall k, forall M M',
    beta_par M M' -> beta_par (lam_k k (Lam M)) (Lam M').
Proof.
  induction k.
  (* k := 0 *)
  intros. simpl. apply beta_par_lam. assumption.
  (* k := (S k) *)

  intros.
  remember H as HH. clear HeqHH. apply IHk in H.
  simpl.
  constructor.
  rewrite shift_0_lam_commute.
  unfold shift. simpl.
  replace M' with (subst 0 (Var 0) (shift 1 M')).
  apply lam_k_beta_subst.
  apply beta_par_shift. assumption.
  apply beta_par_refl.
  apply subst_k_shift_S_k.
Qed.

Lemma lam_k_beta_app:
  forall k, forall M M' N N',
    beta_par M M' -> beta_par N N' ->
      beta_par (App (lam_k k M) N) (App M' N').
Proof.
  induction k.
  (** k := 0 **)
  intros. simpl. apply beta_par_app. assumption. assumption.
  (** k := (S k) **)
  intros.
  rewrite lam_k_alt.
  replace (App M' N') with (subst 0 N' (App (shift 0 M') (Var 0))).
  apply lam_k_beta_subst.
  constructor. apply beta_par_shift. assumption. apply beta_par_refl.
      assumption.
  simpl. rewrite lift_0_ident. rewrite subst_shift_ident. reflexivity.
Qed.

Lemma lam_S_k_beta:
  forall k, forall M M',
    beta_par M M' ->
      beta_par (lam_k (S k) M) (lam_k 1 M').
Proof.
  induction k.
  (** k := 0 **)
  intros. simpl.
  constructor. constructor. apply beta_par_shift. assumption.
  apply beta_par_refl.
  (** k := (S k) **)
  intros.
  rewrite lam_k_alt.
  apply lam_k_beta_lam.
  constructor. apply beta_par_shift. assumption. apply beta_par_refl.
Qed.

Lemma beta_par_lam_k_closed:
  forall k, forall M N,
    beta_par M N -> beta_par (lam_k k M) (lam_k k N).
Proof.
  induction k.
  intros.
  simpl. assumption.
  intros.
  simpl. constructor. constructor. apply beta_par_shift. apply IHk. assumption.
  apply beta_par_refl.
Qed.

Lemma lam_k_eta_red:
  forall k, forall M N,
    eta_par M N -> eta_par (lam_k k M) N.
Proof.
  induction k.
  intros.

  simpl. assumption.

  intros.
  simpl. apply eta_par_base with (lam_k k M).
  reflexivity.
  apply IHk. assumption.
Qed.


Lemma postpone_comm:
  forall M P N,
    eta_par M P -> beta_par P N ->
        (exists P', beta_par M P' /\ eta_par P' N).
Proof.
  intros.
  generalize dependent M.
  rename H0 into H.
  dependent induction H.
  (* [P = (Var n) = N] *)
      intros.
      exists M. split.
      apply beta_par_refl.
      assumption.
  (* [P = (Lam P1)] *)
      intro K.
      intros.
      rename M' into N1.
      rename M into P.
      rename K into M.
      apply eta_par_lam_k_lam in H0.
      do 3 destruct H0.
      rewrite H1; clear H1; clear M.
      apply IHbeta_par in H0.
      do 2 destruct H0.
      exists (Lam x1).
      split.
      apply lam_k_beta_lam. assumption.
      constructor. assumption.

   (* App case *)
      intros MM HH.
      apply eta_par_lam_k_app in HH.
      destruct HH. do 3 destruct H1.
      destruct H2.
      rewrite H3; clear H3; clear MM.
      apply IHbeta_par1 in H1.
      apply IHbeta_par2 in H2.
      do 2 destruct H1.
      do 2 destruct H2.
      (* This feels like a weird choice, but seems to work. *)
      exists (lam_k x (App x2 x3)).
      split.
      Focus 2.
      induction x.
      simpl. constructor; assumption.
      simpl. apply eta_par_base with (lam_k x (App x2 x3)).
      reflexivity. assumption.
      induction x.
      simpl. constructor; assumption.
      simpl. constructor. constructor.
      apply beta_par_shift. assumption. apply beta_par_refl.

   (* subst case *)
      intros.
      apply eta_par_lam_k_app in H1.
      do 4 destruct H1. destruct H2.
      rewrite H3. clear H3. clear M0.
      apply eta_par_lam_k_lam in H1.
      do 3 destruct H1. rewrite H3. clear H3. clear x0.
      apply IHbeta_par1 in H1.
      apply IHbeta_par2 in H2.
      do 2 destruct H1.
      do 2 destruct H2.
      exists (lam_k x (subst 0 x4 x0)).
      split.

      apply beta_par_lam_k_closed.
      apply lam_k_beta_subst. assumption. assumption.

      apply lam_k_eta_red.
      apply eta_par_substitutive.
      assumption.
      assumption.
Qed.

  intros.
  exists M. split.
  apply beta_par_refl.
  assumption.

  intros.
  (* TODO *)
  admit.
  admit.
  admit.
Qed.

Definition beta_eta_star := union lterm bstar eta_star.

Theorem eta_postponement:
  forall M N,
    beta_eta_star M N -> (exists P, bstar M P /\ eta_star P N).
Proof.
  admit.
Qed.


End Postpone.
