Require Import String.

Module Export DeBruijn.

Inductive lterm : Type :=
  | Var : nat -> lterm
  | Lam : lterm -> lterm
  | App : lterm -> lterm -> lterm.

End DeBruijn.

Module PrettyTerm.

Inductive pterm : Type :=
  | Var : string -> pterm
  | Lam : string -> pterm -> pterm
  | App : pterm -> pterm -> pterm.

End PrettyTerm.

(** Useless, but why not have it **)
Fixpoint gfold (f: nat -> nat) (t: lterm) : lterm :=
  match t with
      | Var i => Var (f i)
      | Lam t => Lam (gfold f t)
      | App m n => App (gfold f m) (gfold f n)
  end.
