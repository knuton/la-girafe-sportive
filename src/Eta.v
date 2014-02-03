Require Import Untyped.
Require Import Subst.
Require Import Rels.
Require Import Relation_Operators.
Require Import Relation_Definitions.
Require Import Coq.Structures.Equalities.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Compare_dec.

Module Export Eta.

(** * η-conversion *)

(** We define [eta] conversion as the compatible closure of the [eta_base]
    relation. In literature eta-conversion is usually specified as:

        [[λx. (f x) ~> f]], if [[x]] is not free in [[f]]

    Using de Bruijn indices this corresponds to ensuring that
    [[f]] contains no references to the variable with index [0] (or any of it's
    lifted occurrences), which can be expressed by the condition
        [f = shift 0 g]
    Ensuring that *all* variables in [[g]] are of higher binding level.

    Moreover, after the eta-conversion we have lost one λ binder,
    hence we "un-shift" [[f]] to [[g]].
**)

Inductive eta_prim : lterm -> lterm -> Prop :=
   eta_base (f g: lterm): (f = shift 0 g) -> eta_prim (Lam (App f (Var 0))) g.

(** We defined [eta] as the compatible closure of the primitive relation. **)
Definition eta := clos_compat eta_prim.

(** A couple of examples to make sure our definition works with at least
    the basic cases: **)

Example ex1_eta : eta (\"x" ~> ((\"y" ~> `"y") $ `"x")) (\"x" ~> `"x").
  apply clos_base. apply eta_base. unfold shift. auto.
Qed.

Example ex2_eta: eta (Lam (App (Lam (Lam (Var 1))) (Var 0))) (Lam (Lam (Var 1))).
Proof.
  apply clos_base. apply eta_base. unfold shift. auto.
Qed.

Example ex3_eta: ~ eta (Lam (App (Lam (Var 1)) (Var 0))) (Lam (Var 0)).
Proof.
  unfold not. intros. inversion H.
  inversion H0. discriminate.
  inversion H2. inversion H3.
Qed.

(** We prove a couple of substitution lemmas regarding [eta]. **)

(** [eta_prim] is substitutive (as per Barendregt's definition) **)
Lemma eta_prim_substitutive:
  forall (M N L: lterm) (n: nat),
    eta_prim M N -> eta_prim (subst n L M) (subst n L N).
Proof.
  intros.
  assert (Sn_eq: n + 1 = S n). omega.
  destruct H.
  assert (HH: subst n L (Lam (App f (Var 0))) =
               Lam (App (subst (S n) L f) (Var 0))).
  simpl.
  rewrite Sn_eq. auto.
  rewrite HH.
  apply eta_base.
  unfold shift.
  rewrite lift_lem2. simpl. rewrite H. rewrite Sn_eq.
  unfold shift.
  reflexivity. omega.
Qed.

Lemma eta_substitutive:
  forall (M N L: lterm) (n: nat),
  eta M N -> eta (subst n L M) (subst n L N).
Proof.
  intros. generalize dependent n. generalize dependent L.
  unfold eta.
  induction H.
  intros. apply clos_base. apply eta_prim_substitutive. assumption.
  intros. apply clos_lam. apply IHclos_compat.
  intros. apply clos_appl. apply IHclos_compat.
  intros. apply clos_appr. apply IHclos_compat.
Qed.

(** We now show that [eta] is closed under [lift] **)

Lemma eta_prim_lift_closed:
  forall M N, forall b k,
    eta_prim M N -> eta_prim (lift k b M) (lift k b N).
Proof.
  intros.
  generalize dependent b. generalize dependent k.
  dependent induction H.
  intros. rewrite H.
  simpl.
  case_eq (lt_dec 0 (b+1)).
  intros.
  unfold shift.
  apply eta_base. unfold shift.
  rewrite lift_lift_rev.
  replace (b + 1 - 1) with b by omega. reflexivity.
  omega.
  intros. omega.
Qed.


Lemma eta_lift_closed:
  forall M N, forall b k,
    eta M N -> eta (lift k b M) (lift k b N).
Proof.
  induction M.
  intros.
  inversion_clear H. inversion_clear H0.

  intros.
  inversion_clear H. apply eta_prim_lift_closed  with (b := b) (k := k) in H0.
  constructor. assumption.

  simpl. apply clos_lam. apply IHM. assumption.

  intros.
  inversion_clear H. inversion_clear H0.
  simpl. apply clos_appl. apply IHM1. assumption.
  simpl. apply clos_appr. apply IHM2. assumption.
Qed.

(** * Reflexive-transitive closure of η-conversion *)

Definition eta_star := clos_refl_trans lterm eta.
Definition eta_star_step := rt_step lterm eta.
Definition eta_star_refl := rt_refl lterm eta.
Definition eta_star_trans := rt_trans lterm eta.

(** We now show [eta_star] is closed under all [lterm]s **)

Lemma eta_star_lam_closed:
  forall M N,
    eta_star M N -> eta_star (Lam M) (Lam N).
Proof.
  intros.
  dependent induction H.
  constructor.
  apply clos_lam in H. assumption. apply rt_refl.
  apply rt_trans with (Lam y); assumption.
Qed.

Lemma eta_star_app_closed_l:
  forall M M' N,
    eta_star M M' -> eta_star (App M N) (App M' N).
Proof.
  intros.
  dependent induction H.
  constructor. apply clos_appl. assumption.
  apply rt_refl.
  apply rt_trans with (App y N); assumption.
Qed.

Lemma eta_star_app_closed_r:
  forall M N N',
    eta_star N N' -> eta_star (App M N) (App M N').
Proof.
  intros.
  dependent induction H.
  constructor. apply clos_appr. assumption.
  apply rt_refl.
  apply rt_trans with (App M y); assumption.
Qed.

Lemma eta_star_app_closed:
  forall M M' N N',
    eta_star M M' -> eta_star N N' -> eta_star (App M N) (App M' N').
Proof.
  intros ? ? ? ?. intros H1 H2.
  apply rt_trans with (App M N').
  apply eta_star_app_closed_r. assumption.
  apply eta_star_app_closed_l. assumption.
Qed.

(** Additionally, [eta_star] is closed under lifting **)
Lemma eta_star_lift_closed:
  forall M N, forall k b,
    eta_star M N -> eta_star (lift k b M) (lift k b N).
Proof.
  intros.
  dependent induction H.
  constructor. apply eta_lift_closed. assumption.
  apply eta_star_refl.
  apply eta_star_trans with (lift k b y).
  assumption. assumption.
Qed.

(** Finally, we show that [eta_star] is closed under the same primitive
    relation as [eta] **)

Lemma eta_star_base_closed:
  forall M N N',
    (M = shift 0 N) -> eta_star N N' ->
          eta_star (Lam (App M (Var 0))) N'.
Proof.
  intros.
  rewrite H. clear H. clear M.
  dependent induction H0.
  apply rt_trans with (Lam (App (shift 0 y) (Var 0))).
  apply eta_star_lam_closed. apply eta_star_app_closed.
  apply eta_star_lift_closed. constructor. assumption.
  apply rt_refl.
  constructor. apply clos_base. apply eta_base. reflexivity.
  constructor. apply clos_base. apply eta_base. reflexivity.

  apply rt_trans with (Lam (App (shift 0 y) (Var 0))).
  apply eta_star_lam_closed. apply eta_star_app_closed.
  apply eta_star_lift_closed. assumption. apply rt_refl.
  assumption.
Qed.

(** * Parallel [eta] conversion *)

(** We now define parallel eta conversion [eta_par],
    it is a trivial translation from the one in the paper, except for the case
    [eta_par_base], in which one needs to do the same translation as for
    [eta_prim].
**)

Inductive eta_par : lterm -> lterm -> Prop :=
  | eta_par_var: forall n,
        eta_par (Var n) (Var n)
  | eta_par_lam: forall M M',
        eta_par M M' -> eta_par (Lam M) (Lam M')
  | eta_par_app: forall M M' N N',
        eta_par M M' -> eta_par N N' -> eta_par (App M N) (App M' N')
  | eta_par_base: forall M N N',
        (M = shift 0 N) -> eta_par N N' ->
          eta_par (Lam (App M (Var 0))) N'.


(** Some general properties about [eta_par] **)

(** Parallel eta is reflexive on all [lterm]s **)
Lemma eta_par_refl:
  forall t, eta_par t t.
Proof.
  induction t.
  constructor.
  apply eta_par_lam.
  assumption.
  apply eta_par_app.
  assumption. assumption.
Qed.

(** Parallel eta is closed under lifting **)
Lemma eta_par_lift_closed:
  forall M N, forall k b,
    eta_par M N -> eta_par (lift k b M) (lift k b N).
Proof.
  intros.
  generalize dependent k.
  generalize dependent b.
  dependent induction H.
  intros. apply eta_par_refl.
  simpl. intros. constructor. apply IHeta_par.
  simpl. intros. constructor. apply IHeta_par1. apply IHeta_par2.

  simpl. intros.
  replace (b +1) with (S b) by omega. simpl.
  unfold shift. replace (S b) with (b+1) by omega.
  rewrite H.
  apply eta_par_base with (lift k b N).
  unfold shift. replace (S b) with (b+1) by omega.
  rewrite lift_lift_rev. replace (b+1-1) with b by omega.
  reflexivity. omega.
  apply IHeta_par.
Qed.

(** [eta_par] is substitutive **)
Lemma eta_par_substitutive:
  forall (M N L: lterm) (n: nat),
  eta_par M N -> eta_par (subst n L M) (subst n L N).
Proof.
  intros. generalize dependent n.
  dependent induction H.
  intros. apply eta_par_refl.
  simpl. constructor. apply IHeta_par.
  simpl. constructor. apply IHeta_par1. apply IHeta_par2.
  intros.
  simpl. replace (n+1) with (S n) by omega.
  rewrite H. replace (S n) with (n+1) by omega.
  rewrite <- lift_lem2.
  apply eta_par_base with (subst n L N). reflexivity.
  apply IHeta_par. omega.
Qed.

(** [eta_par] is fully closed under parallel substitution **)
Lemma eta_par_subst_closed:
  forall (M M' N N': lterm), forall n,
    eta_par M M' -> eta_par N N' -> eta_par (subst n N M) (subst n N' M').
Proof.
  intros. generalize dependent n.
  dependent induction H. intros. simpl.
  case_eq (nat_compare n n0).
  intros.
  apply eta_par_lift_closed. assumption.
  intros. apply eta_par_refl.
  intros. apply eta_par_refl.

  intros. simpl. apply eta_par_lam. apply IHeta_par. assumption.
  intros. simpl. apply eta_par_app. apply IHeta_par1. assumption.
                                    apply IHeta_par2. assumption.

  intros.
  simpl. replace (n+1) with (S n) by omega. simpl.
  rewrite H. simpl.
  apply eta_par_base with (subst n N N0).
  unfold shift. replace (S n) with (n+1) by omega.
  rewrite lift_lem2. reflexivity.
  omega.
  apply IHeta_par. assumption.
Qed.

(** We now describe the relationships between [eta], [eta_par] and [eta_star] **)

(** [eta] implies [eta_par] **)
Lemma eta_imp_eta_par:
  forall M N, eta M N -> eta_par M N.
Proof.
  intros.
  dependent induction H.
  destruct H. apply eta_par_base with g. assumption.
  apply eta_par_refl.
  constructor. assumption.
  constructor. assumption. apply eta_par_refl.
  constructor. apply eta_par_refl. assumption.
Qed.

(** [eta_par] implies [eta_star] **)
Lemma eta_par_imp_eta_star:
  forall M N,
    eta_par M N -> eta_star M N.
Proof.
  intros.
  dependent induction H.
  apply rt_refl.
  apply eta_star_lam_closed. assumption.
  apply eta_star_app_closed; assumption.
  apply eta_star_base_closed with N; assumption.
Qed.

(** The transitive closure of [eta_par] **)
Definition eta_par_trans := clos_trans lterm eta_par.

(** Finally, we show that [eta_star] is equivalent to the transitive closure of
    [eta_par] **)
Lemma eta_star_eq_closure_of_eta_par:
  forall M N,
    eta_star M N <-> eta_par_trans M N.
Proof.
  split.

  intros.
  dependent induction H.
  constructor. apply eta_imp_eta_par. assumption.
  constructor. apply eta_par_refl.
  apply t_trans with y; assumption.

  intros.
  dependent induction H.
  apply eta_par_imp_eta_star. assumption.

  apply rt_trans with y; assumption.
Qed.


(** We now define a function for expressing a [k]-fold [eta] expansion of
    an [lterm]. **)
Fixpoint lam_k (k: nat) (M: lterm) : lterm :=
  match k with
    | 0 => M
    (*
     Note: This should have probably been defined in a tail-recursive way, as:

      [ (S n) => lam_k (App (shift 0 M) (Var 0)) ]

      since it is much easier to work with. However,
      I realised this way too late, so left it this way in order to avoid
      modifying existing proofs. Instead, an equivalence of these definitions
      is proved in the [lam_k_alt] lemma.
    *)
    | (S n) => Lam (App (shift 0 (lam_k n M)) (Var 0))
  end.

Lemma lam_k_alt:
  forall k, forall M,
    lam_k (S k) M = lam_k k (Lam (App (shift 0 M) (Var 0))).
Proof.
  induction k.
  intros. simpl. reflexivity.
  intros.
  simpl. do 4 f_equal. rewrite <- IHk. simpl.
  reflexivity.
Qed.

(** A trivial fact **)
Example lam_k_zero:
  forall M, lam_k 0 M = M.
Proof.
  auto.
Qed.

(** This commutativity lemma which will be useful later. **)
Lemma shift_0_lam_commute:
    forall n, forall t,
      shift 0 (lam_k n t) = (lam_k n (shift 0 t)).
Proof.
    induction n.
    (* [n := 0] *)
        simpl. reflexivity.
    (* [n := (S n)] *)
        intros. simpl. unfold shift. simpl.
        f_equal. f_equal.
        rewrite lift_fuse. simpl. rewrite <- IHn. unfold shift.
        rewrite lift_fuse. simpl.
        reflexivity. simpl. auto. simpl. auto.
Qed.


(** We now prove some basic properties about the relationship between [[eta]]
    and [[lam_k]]. (This is Lemma 3.2 in the Takahashi paper.) **)

(* Lemma 3.2 (1) *)
Lemma eta_par_lam_k_var:
  forall M, forall n,
    eta_par M (Var n) <-> (exists k, M = lam_k k (Var n)).
Proof.
  intros. split.
  (* -> *)
      (* trivial induction on the definition of [eta_par] *)
      intros.
      dependent induction H.
      exists 0.
      apply lam_k_zero.
      destruct IHeta_par.
      rewrite H.
      exists (S x). simpl. f_equal.
  (* <- *)
      intros.
      (* clean up our hypothesis a bit *)
      destruct H.
      rewrite H.
      clear H. clear M.
      generalize dependent n.
      generalize dependent x.
      (* again, just perform simple induction on [k] *)
      intro k.
      induction k.
          intros.
          simpl.
          apply eta_par_var.

          intros.
          simpl.
          apply eta_par_base with (lam_k k (Var n)).
          reflexivity.
          apply IHk.
Qed.

(* Lemma 3.2 (2), the proof technique is essentially the same as for
   [eta_par_lam_k_var].
*)
Lemma eta_par_lam_k_app:
  forall M N_1 N_2,
    eta_par M (App N_1 N_2)
    <->
    (exists k, exists M_1 M_2,
         (eta_par M_1 N_1) /\ (eta_par M_2 N_2) /\  M = lam_k k (App M_1 M_2)).
Proof.
  split.
    (* -> *)
    intro.
    dependent induction H.
    exists 0. simpl.
    exists M.
    exists N.
    split.
    assumption.
    split.
    assumption.
    reflexivity.
    destruct IHeta_par.
    exists (S x).
    simpl.
    destruct H as [M_1].
    destruct H as [M_2].
    exists M_1.
    exists M_2.
    split. destruct H.
    assumption.
    destruct H. destruct H1.
    split. assumption.
    apply f_equal.
    f_equal. rewrite H2. reflexivity.
    (* <- *)
    intros.
    destruct H as [k].
    generalize dependent M.
    generalize dependent N_1.
    generalize dependent N_2.
    induction k.
    (* [k := 0] *)
        intros.
        destruct H as [M_1].
        destruct H as [M_2].
        destruct H as [H1].
        destruct H as [H2].
        rewrite H.
        simpl. apply eta_par_app. assumption. assumption.
    (* [k := (S k)] *)
        intros.
        simpl in H.
        destruct H as [M_1].
        destruct H as [M_2].
        destruct H as [H1].
        destruct H as [H2].
        rewrite H.
        apply eta_par_base with (lam_k k (App M_1 M_2)).
        reflexivity.
        apply IHk.
        exists M_1.
        exists M_2.
        split. assumption.
        split. assumption.
        reflexivity.
Qed.


(* Lemma 3.2 (3), the situation is again similar to the previous two
    cases *)
Lemma eta_par_lam_k_lam:
  forall M N,
        eta_par M (Lam N)
        <->
        (exists k, exists M', (eta_par M' N) /\ (M = lam_k k (Lam M'))).
Proof.
  split.
  (* -> *)
    intro.
    dependent induction H.
    exists 0. exists M.
    split. assumption.
    simpl. reflexivity.
    destruct IHeta_par as [k].
    destruct H as [M'].
    destruct H as [H1].
    exists (S k).
    exists M'.
    split. assumption.
    simpl. rewrite H. f_equal.

  (* <- *)
    intros.
    destruct H as [k].
    generalize dependent M.
    generalize dependent N.
    induction k.
    (* [k := 0] *)
        intros. destruct H as [M'].
        destruct H as [H1].
        rewrite H.
        simpl. apply eta_par_lam. assumption.

    (* [k := (S k)] *)
        intros.
        destruct H as [M'].
        destruct H as [H1].
        rewrite H.
        simpl.
        apply eta_par_base with (lam_k k (Lam M')).
        reflexivity.
        apply IHk.
        exists M'.
        split. assumption.
        reflexivity.
Qed.

(** Finally, we include this simple lemma which will be useful later. **)

(* Parallel eta is closed under eta-expansion in the co-domain *)
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

End Eta.
