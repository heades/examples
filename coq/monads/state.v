Require Import monad.

Inductive State (S A : Type) :=
 | state : (S -> (A * S)) -> State S A.

Definition run {S A : Type} (m : State S A) : (S -> (A * S)) :=
  match m with
    | state a => a
  end.

(* State is a monad. *)
Parameter S : Type.

Instance State_Monad : Monad (State S) := {
  bind a b i f := 
    state S b (fun s => 
      let x := run i s in 
        match x with
          | (x', s') => run (f x') s' 
        end);

  ret A a := state S A (fun s => (a, s))
}.

Require Import FunctionalExtensionality.
Proof.
  intros a b c f.
  simpl; destruct (f c); simpl; reflexivity.

  intros a m'.
  destruct m'.
  simpl. 
  rewrite -> (functional_extensionality (fun s : S => let (x', s') := p s in (x', s')) p).
  reflexivity.
  intros x.
  destruct (p x).
  reflexivity.

  intros a b c i f g.
  simpl.
  f_equal.
  destruct i.
  extensionality s.
  simpl.
  destruct (p s).
  reflexivity.
Defined.
