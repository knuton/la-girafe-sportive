Require Import Untyped.
Require Import Subst.
Require Import Relation_Operators.

Module Rels.

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

End Rels.