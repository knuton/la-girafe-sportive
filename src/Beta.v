Require Import Untyped.
Require Import Subst.
Require Import Relation_Operators.
Require Import Coq.Program.Equality.


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

End Beta.
