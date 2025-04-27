Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From SetsClass Require Import SetsClass.
From MonadErr Require Import MonadErrBasic MonadErrLoop MonadErrHoare.
From SetMonad Require Import Monad.

Local Open Scope Z_scope.
Import SetsNotation.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

Import MonadErr.
Export MonadNotation.
Local Open Scope monad.

(** This is the KMP program in MonadErr used for C program verification with refinement proof *)

Section inner_loop_monad.

Context {A: Type}
        (default: A)
        (str: list A)
        (next: list Z)
        (ch: A).

Definition Znth {A: Type} (i: Z) (l: list A) (default: A): A :=
  nth (Z.to_nat i) l default.

Definition inner_body: Z -> program unit (CntOrBrk Z Z) :=
  fun j =>
    assert (0 <= j < Zlength str);;
    assert (j < Zlength next);;
    choice (assume(ch = Znth j str default);;
            break (j + 1))
            (assume(ch <> Znth j str default);;
            choice (assume(j = 0);;
                    break(0)) 
                    (assume(j <> 0);;
                    continue (Znth (j-1) next 0))).

Definition inner_loop: Z -> program unit Z :=
  repeat_break inner_body.

End inner_loop_monad.

Section constr_loop_monad.

Context {A: Type}
        (default: A)
        (str: list A).

Definition constr_body:
  Z -> list Z * Z -> program unit (list Z * Z) :=
  fun i =>
    fun '(next, j) =>
      assert (i < Zlength str);;
      let ch := Znth i str default in
      j' <- inner_loop default str next ch j;;
      ret (next ++ [j'], j').

Definition constr_loop: program unit (list Z) :=
  '(next, j) <- range_iter 1 (Zlength str) constr_body ([0], 0);;
  ret next.

End constr_loop_monad.

Section match_loop_monad.

Context {A: Type}
        (default: A)
        (patn text: list A)
        (next: list Z).

Definition match_body:
  Z -> Z -> program unit (CntOrBrk Z Z) :=
  fun i j =>
      assert (i < Zlength text);;
      let ch := Znth i text default in
      j' <- inner_loop default patn next ch j;;
      choice
        (assume (j' = Zlength patn);;
         break (i - Zlength patn + 1))
        (assume (j' < Zlength patn);;
         continue (j')).

Definition match_loop: program unit (option Z) :=
  res <- range_iter_break 0 (Zlength text) match_body 0;;
  match res with
  | by_continue _ => ret None
  | by_break i => ret (Some i)
  end.

End match_loop_monad.

(** The proof is essentially same with KMP in SetMonad. *)
