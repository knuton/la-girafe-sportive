Require Import Relation_Operators.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Compare_dec.

Require Import Untyped.
Require Import Subst.

Module Export Beta.

(** * β-reduction *)

Inductive bred : lterm -> lterm -> Prop :=
  | bred_base : forall t1 t2,
      bred (App (Lam t1) t2) (subst 0 t2 t1)
  | bred_lam  : forall t1 t2,
      bred t1 t2 -> bred (Lam t1) (Lam t2)
  | bred_appl : forall t1 t2 t3,
      bred t1 t2 -> bred (App t1 t3) (App t2 t3)
  | bred_appr : forall t1 t2 t3,
      bred t1 t2 -> bred (App t3 t1) (App t3 t2).

(** Consider the following two examples of one-step beta reduction.
*)

Example triv_bred : bred ((\"x" ~> `"x") $ `"y") (`"y").
Proof. apply bred_base. Qed.

Example inner_bred :
  bred ((\"x" ~> (\"y" ~> `"x" $ `"y") $ `"z") $ `"y") ((\"x" ~> `"x" $ `"z") $ `"y").
Proof. apply bred_appl. apply bred_lam. apply bred_base. Qed.

Lemma bred_lift_closed:
  forall M N, forall b k,
    bred M N -> bred (lift k b M) (lift k b N).
Proof.
  induction M.
  intros.
  inversion_clear H.

  intros.
  inversion_clear H.
  simpl.
  constructor.
  apply IHM. assumption.

  intros.
  inversion_clear H.
  simpl.
  rewrite lift_subst_semicom.
  apply bred_base. omega.

  simpl. constructor. auto.

  simpl. constructor. auto.
Qed.

(** * Reflexive-transitive closure of beta reduction *)

Definition bstar := clos_refl_trans lterm bred.
Definition bstar_step := rt_step lterm bred.
Definition bstar_refl := rt_refl lterm bred.
Definition bstar_trans := rt_trans lterm bred.

(** Again, we consider a simple example of the multi-step reduction relation.
*)

Example bred_halt :
  bstar ((\"x" ~> (\"y" ~> `"x" $ `"y") $ `"z") $ `"y") (`"y" $ `"z").
Proof.
  apply bstar_trans with ((\"x" ~> `"x" $ `"z") $ `"y").
  apply bstar_step. apply inner_bred.
  apply bstar_step. apply bred_base.
Qed.

Lemma bstar_reflexive:
  forall M, bstar M M.
Proof.
  apply rt_refl.
Qed.

Lemma bstar_lam_closed:
  forall M N,
    bstar M N -> bstar (Lam M) (Lam N).
Proof.
  intros.
  dependent induction H.
  constructor. constructor. assumption.
  apply rt_refl.
  apply rt_trans with (Lam y); assumption.
Qed.

Lemma bstar_app_closed_l:
  forall M M' N,
    bstar M M' -> bstar (App M N) (App M' N).
Proof.
  intros.
  dependent induction H.
  constructor. constructor. assumption.
  apply rt_refl.
  apply rt_trans with (App y N); assumption.
Qed.

Lemma bstar_app_closed_r:
  forall M N N',
    bstar N N' -> bstar (App M N) (App M N').
Proof.
  intros.
  dependent induction H.
  constructor. constructor. assumption.
  apply rt_refl.
  apply rt_trans with (App M y); assumption.
Qed.

Lemma bstar_app_closed:
  forall M M' N N',
    bstar M M' -> bstar N N' -> bstar (App M N) (App M' N').
Proof.
  intros ? ? ? ?. intros H1 H2.
  apply rt_trans with (App M N').
  apply bstar_app_closed_r. assumption.
  apply bstar_app_closed_l. assumption.
Qed.

Lemma bstar_subst_closed_l:
  forall M M' N,
         bstar M M' -> bstar (App (Lam M) N) (subst 0 N M').
Proof.
  intros.
  dependent induction H.
  apply rt_trans with (App (Lam y) N).
  apply bstar_app_closed. apply bstar_lam_closed. constructor. assumption.
  apply rt_refl. apply rt_step. apply bred_base.
  constructor. apply bred_base.
  apply rt_trans with (App (Lam y) N).
  apply bstar_app_closed. apply bstar_lam_closed. assumption.
  apply rt_refl.
  assumption.
Qed.

Lemma bstar_lift_closed:
  forall M N, forall b k,
    bstar M N -> bstar (lift k b M) (lift k b N).
Proof.
  intros.

  dependent induction H.

  constructor. apply bred_lift_closed. assumption.

  apply rt_refl.

  apply rt_trans with (lift k b y); assumption.
Qed.


Lemma bstar_weak_subst:
  forall M, forall k, forall N N',
    bstar N N' -> bstar (subst k N M) (subst k N' M).
Proof.
  dependent induction M.
  intros.
  simpl.
  case_eq (nat_compare n k).
  rewrite nat_compare_eq_iff. intros.
  apply bstar_lift_closed. assumption.

  intros. apply rt_refl.
  intros. apply rt_refl.


  intros.
  simpl. apply bstar_lam_closed. apply IHM. assumption.

  intros.
  simpl. apply bstar_app_closed; auto.
Qed.


Lemma bstar_subst_closed_r:
  forall M N N',
         bstar N N' -> bstar (App (Lam M) N) (subst 0 N' M).
Proof.
  intros.
  dependent induction H.
  apply rt_trans with (subst 0 x M).
  apply rt_step. apply bred_base.
  apply bstar_weak_subst. constructor. assumption.

  apply rt_step. constructor.
  apply rt_trans with (App (Lam M) y).
  apply bstar_app_closed.
  apply bstar_lam_closed.
  apply bstar_reflexive.
  assumption.

  assumption.
Qed.


Lemma bstar_subst_closed:
  forall M M' N N',
   bstar M M' -> bstar N N' -> bstar (App (Lam M) N) (subst 0 N' M').
Proof.
  intros.
  apply rt_trans with (App (Lam M) N').
  apply bstar_app_closed. apply bstar_lam_closed. apply rt_refl. assumption.
  apply bstar_subst_closed_l. assumption.
Qed.


(** * Parallel [beta] reduction *)
Inductive beta_par : lterm -> lterm -> Prop :=
  | beta_par_var: forall n,
        beta_par (Var n) (Var n)
  | beta_par_lam: forall M M',
        beta_par M M' -> beta_par (Lam M) (Lam M')
  | beta_par_app: forall M M' N N',
        beta_par M M' -> beta_par N N' -> beta_par (App M N) (App M' N')
  | beta_par_base: forall M M' N N',
        beta_par M M' ->
        beta_par N N' ->
        beta_par (App (Lam M) N) (subst 0 N' M').

(** A couple of useful results about [beta_par] **)

(** Parallel beta reduction is reflexive on all [lterm]'s **)
Lemma beta_par_refl:
  forall t, beta_par t t.
Proof.
  induction t.
  apply beta_par_var.
  apply beta_par_lam.
  apply IHt.
  apply beta_par_app.
  assumption.
  assumption.
Qed.

(** Parallel beta subsumes beta **)
Lemma bred_imp_beta_par:
  forall M N,
    bred M N -> beta_par M N.
Proof.
  intros.
  dependent induction H;
  constructor; try apply beta_par_refl; try assumption.
Qed.

Lemma beta_par_imp_bstar:
  forall M N,
    beta_par M N -> bstar M N.
Proof.
  intros.
  dependent induction H.
  apply rt_refl.
  apply bstar_lam_closed. assumption.
  apply bstar_app_closed; assumption.
  apply bstar_subst_closed; assumption.
Qed.

(** [beta_par] is closed under [shift k] **)
Lemma beta_par_shift:
  forall k, forall M M', beta_par M M' -> beta_par (shift k M) (shift k M').
Proof.
  intros.
  generalize dependent k.
  dependent induction H.
  intros. apply beta_par_refl.
  intros. unfold shift. simpl. apply beta_par_lam.
      apply IHbeta_par.
  intros. unfold shift. simpl. constructor.
      apply IHbeta_par1.
      apply IHbeta_par2.
  intros.
  unfold shift. simpl. rewrite lift_subst_semicom.
  replace (lift 1) with shift.
  apply beta_par_base.
      apply IHbeta_par1.
      apply IHbeta_par2.
  reflexivity.
  omega.
Qed.

Definition beta_par_trans := clos_trans lterm beta_par.

Lemma bstar_eq_closure_of_beta_par:
  forall M N,
    bstar M N <-> beta_par_trans M N.
Proof.
  split.

  intros.
  dependent induction H.
  constructor. apply bred_imp_beta_par. assumption.
  constructor. apply beta_par_refl.
  apply t_trans with y; assumption.

  intros.
  dependent induction H.
  apply beta_par_imp_bstar. assumption.

  apply rt_trans with y; assumption.
Qed.

End Beta.
