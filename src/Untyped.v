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