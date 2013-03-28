Require Import monad.

Inductive Maybe (A:Type) : Type :=
  | Just : A -> Maybe A
  | None : Maybe A.

(* Maybe is a monad.*)
Instance Maybe_Monad : Monad Maybe := {
  bind a b i f := match i with
               | Just c => (f c)
               | None => None b
              end;
  
  ret a := Just a
}.

(* Proofs of the monad laws. *)
Proof.
  reflexivity.
  
  intros a m'.
  destruct m'; auto.

  intros a b c i f g.
  destruct i; auto.
Defined.

(* Maybe is a functor. *)
Definition Maybe_Functor := Monad_Functor Maybe Maybe_Monad.
Definition maybe_fmap {a b : Type} {F : Functor Maybe} (f:a -> b) x := fmap f x. 
Check maybe_fmap.