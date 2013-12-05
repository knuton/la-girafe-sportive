Require Import String.
Require Import List.
Require Import Coq.Arith.EqNat.

Module Export DeBruijn.

Inductive lterm : Type :=
  | Var : nat -> lterm
  | Lam : lterm -> lterm
  | App : lterm -> lterm -> lterm.

(** Useless, but why not have it **)
Fixpoint gfold (f: nat -> nat) (t: lterm) : lterm :=
  match t with
      | Var i => Var (f i)
      | Lam t => Lam (gfold f t)
      | App m n => App (gfold f m) (gfold f n)
  end.

End DeBruijn.

Module PrettyTerm.

Inductive pterm : Type :=
  | Var : string -> pterm
  | Lam : string -> pterm -> pterm
  | App : pterm -> pterm -> pterm.

End PrettyTerm.

(** We introduce some notational conveniences for pretty lambda terms. **)

Notation "` x" := (PrettyTerm.Var x) (at level 20).
Notation "\ x ~> M" := (PrettyTerm.Lam x M) (at level 30).
Infix "$" := PrettyTerm.App (at level 25, left associativity).

Check \"f" ~> `"f" $ \"x" ~> `"x" $ `"y" $ `"z".

(** TODO There is some problem with operator precedence with [=]. *)
Example prettier :
  (\"f" ~> `"f" $ \"x" ~> `"x" $ `"y") =
  PrettyTerm.Lam "f"
    (PrettyTerm.App
      (PrettyTerm.Var "f")
      (PrettyTerm.Lam "x"
        (PrettyTerm.App
          (PrettyTerm.Var "x")
          (PrettyTerm.Var "y")))).
Proof. simpl. reflexivity. Qed.

(** Since we don't really want to work with pretty (named) terms, we provide a function
    [dename] for converting pretty terms to De Bruijn terms.
*)

Fixpoint lookup (s: string) (ls: list (string * nat)) : option nat :=
  match ls with
  | nil => None
  | (x, n) :: t => if string_dec x s then Some n else lookup s t
  end.

Fixpoint hide (s: string) (ls: list (string * nat)) : list (string * nat) :=
  match ls with
  | nil => (s, 0) :: nil
  | (x, n) :: t => if string_dec x s then (x, 0) :: t else (x, n + 1) :: hide s t
  end.

Fixpoint dename1 (t: PrettyTerm.pterm) (binds: list (string * nat)) : lterm :=
  match t with
  | PrettyTerm.Var s => match lookup s binds with
             | Some n => Var n
             | None => Var 0
             end
  | PrettyTerm.Lam s t => Lam (dename1 t (hide s binds))
  | PrettyTerm.App t1 t2 => App (dename1 t1 binds) (dename1 t2 binds) 
  end.

Definition dename (t : PrettyTerm.pterm) : lterm :=
  dename1 t nil.

(** To convince ourselves of the correctness of [dename], let us briefly look at what
    it does to the combinators K and S.
*)

Example k_comb : dename (\"x" ~> \"y" ~> `"x") = Lam (Lam (Var 1)).
Proof. reflexivity. Qed.

Example s_comb :
  dename (\"x" ~> \"y" ~> \"z" ~> `"x" $ `"z" $ (`"y" $ `"z")) =
  Lam (Lam (Lam (App (App (Var 2) (Var 0)) (App (Var 1) (Var 0))))).
Proof. reflexivity. Qed.