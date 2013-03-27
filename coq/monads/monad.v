(* License: 
     "THE BEER-WARE LICENSE" (Revision 42):
     As long as you retain this notice you can do whatever you want with
     this stuff. If we meet some day, and you think this stuff is worth it,
     you can buy me a beer in return Harley Eades. *)

Require Import String.

Reserved Notation "m '>>=' f" (at level 40). 
Reserved Notation "m '>>' f" (at level 40). 

Class Monad (m : Type -> Type) := {
  (* Monad Core. *)
  
  (* bind - Used for chaining. *)
  bind : forall {a} {b}, m a -> (a -> m b) -> m b
    where "m '>>=' f" := (bind m f);

  (* return - The injector of our monad. *)
  ret : forall {a}, a -> m a;

  (* Extras. *)
  
  (* bind_ign - Like bind, but ignores the argument. *)
  bind_ign : forall {a} {b}, m a -> m b -> m b
    where "m '>>' f" := (bind m f);

  (* fail_m - Used to break a chain. *)
  fail_m : forall {a}, string -> m a;

  (* Monads Laws. *)

  (* Left identity. *)
  left_id : forall a b c (f : a -> m b), 
    (ret c) >>= f = (f c);
  
  (* Right identity. *)
  right_id : forall (a : Type) (m' : m a), 
    m' >>= ret = m';

  (* Associativity. *)
  assoc : forall (a b c : Type)  (i : m a) (f : a -> m b) (g : b -> m c), 
    (i >>= f) >>= g = i >>= (fun x => ((f x) >>= g))
}.

(* Monads are functors. *)
Definition comp {a b c:Type} (f:b -> c) (g:a -> b) := fun x => f (g x).

Class Functor (f : Type -> Type) := {
  fmap : forall {a b}, (a -> b) -> f a -> f b;

  (* Functor Axioms. *)
  id : forall (a : Type), fmap (fun (x:a) => x) = (fun (x: f a) => x);

  compo : forall (a b c:Type) (p : b -> c) (q : a -> b), fmap (comp p q) = comp (fmap p) (fmap q)
}.

Instance Monad_Functor : forall m (i: Monad m), Functor m := {
  fmap a b f fa := bind fa (fun (x:a) => (ret (f x)))
}.

Require Import FunctionalExtensionality.
Proof.
  intros a.
  rewrite <- (eta_expansion ret).
  extensionality x.
  apply right_id.

  intros a b c p q.
  unfold comp.
  extensionality x.
  rewrite -> assoc.
  apply f_equal.
  extensionality x0.
  rewrite -> left_id.
  reflexivity.
Defined.


