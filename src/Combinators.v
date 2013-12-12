Require Import Untyped.
Require Import Subst.
Require Import Beta.

Module Export Combinators.

Definition I :=
  \"x" ~> `"x".
Definition K :=
  \"x" ~> \"y" ~> `"x".
Definition S :=
  \"x" ~> \"y" ~> \"z" ~> `"x" $ `"z" $ (`"y" $ `"z").
Definition Y :=
  \"f" ~> (\"x" ~> `"f" $ (`"x" $ `"x")) $ (\"x" ~> `"f" $ (`"x" $ `"x")). 

Lemma skk_i : bstar (S $ K $ K) I.
Proof.
  unfold S. unfold I.
  apply bstar_trans with (\"z" ~> (\"y" ~> `"z") $ (K $ `"z")).
  apply bstar_trans with (\"z" ~> K $ `"z" $ (K $ `"z")).
  apply bstar_trans with ((\"y" ~> \"z" ~> K $ `"z" $ (`"y" $ `"z")) $ K).
  apply bstar_step. apply bred_appl. apply bred_base.
  apply bstar_step. apply bred_base.
  apply bstar_step. apply bred_lam. apply bred_appl. apply bred_base.
  apply bstar_step. apply bred_lam. apply bred_base.
Qed.

End Combinators.