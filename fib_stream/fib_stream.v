Require Import Arith.

CoInductive nat_stream : Set :=
  | Cons : nat -> nat_stream -> nat_stream.

Definition head (s:nat_stream) : nat := 
  match s with
    | Cons n _ => n
  end.

Definition tail (s:nat_stream) : nat_stream :=
  match s with
    | Cons _ t => t
  end.

Fixpoint nth_el (n:nat) (s:nat_stream) : nat :=
  match n with
    | 0 =>   head s
    | S m => nth_el m (tail s)
  end.

CoFixpoint fib_stream_aux (n:nat) (m:nat) : nat_stream := Cons (n+m) (fib_stream_aux (n+m) n).
Definition fib_stream := Cons 0 (Cons 1 (fib_stream_aux 1 0)).

Eval compute in nth_el  0 fib_stream.
Eval compute in nth_el  1 fib_stream.
Eval compute in nth_el  2 fib_stream.
Eval compute in nth_el  3 fib_stream.
Eval compute in nth_el  4 fib_stream.
Eval compute in nth_el  5 fib_stream.
Eval compute in nth_el  6 fib_stream.
Eval compute in nth_el  7 fib_stream.
Eval compute in nth_el  8 fib_stream.
Eval compute in nth_el  9 fib_stream.
Eval compute in nth_el 10 fib_stream.
(* Largest we can go before coqtop segmentation faults. *)
Eval compute in nth_el 25 fib_stream.
