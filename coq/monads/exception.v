Require Import monad.

Inductive Exceptional (e a : Type) :=
  | success : a -> Exceptional e a
  | exception : e -> Exceptional e a.

Parameter e : Type.

Instance Exceptional_Monad : Monad (Exceptional e) := {
  bind a b i f := 
    match i with
      | success k   => f k
      | exception l => exception e b l
    end;
  ret a := success e a
}.

Proof.
  reflexivity.

  intros a m'; destruct m'; reflexivity.

  intros a b c i f g; destruct i; reflexivity.
Defined.

Parameter a : Type.
Definition throw := exception.
Definition catch (g : Exceptional e a) (h : e -> Exceptional e a)  : Exceptional e a :=
  match g with
    | exception l => h l
    | _ => g
  end.
