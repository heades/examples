Section Inf_List.
Require Import Arith.

CoInductive inf_list : Set :=
  | inf_cons : nat -> inf_list -> inf_list.

Definition head (l:inf_list) :=
  match l with
    | inf_cons n l' => n
  end.

Definition tail (l:inf_list) :=
  match l with
    | inf_cons n l' => l'
  end.

CoFixpoint ext (f : nat -> nat) (l : inf_list) : inf_list :=
  match l with
    | inf_cons n l' => inf_cons (f n) (ext f l')
  end.
(** Notice that this definition fits the pattern on page 9 of 
    Jacobs:1997.  That is 
        [head(ext f l) = f (head l)]
        [tail(ext f l) = ext f (tail l)].
    In fact the proof of this claim is trivial. *)
Lemma ext_fits_coind_pattern : forall f l,
  head (ext f l) = f (head l) /\
  tail (ext f l) = ext f (tail l).
Proof.
  auto.
  Restart.
  intros; destruct l; split; reflexivity.
Qed.
(** Our pattern above tells us that we can actually define
    [ext] interms of [head] and [tail]. *)
Reset ext.
CoFixpoint ext (f : nat -> nat) (l : inf_list) : inf_list := 
  inf_cons (f (head l)) (ext f (tail l)).

(** Next we define the definition of a co-inductive function called odd.
    It takes an infinite list and produces the infinite list containing 
    the elements at odd positions in the input list *)
CoFixpoint odd (l : inf_list) : inf_list := inf_cons (head l) (tail (tail l)).
(** We can also define [even], but this is easy.  *)
Definition even (l: inf_list) : inf_list := odd (tail l).

(** The following co-inductive function merges two [inf_list]'s into a single
    [inf_list] in turn starting with the first. *)
CoFixpoint merge (l1 : inf_list) (l2 : inf_list) : inf_list :=
  inf_cons (head l1) (merge l2 (tail l1)).
(** This definition is equivalent to the following: *)
Reset merge.
CoFixpoint merge (l1 : inf_list) (l2 : inf_list) : inf_list :=
  inf_cons (head l1) (inf_cons (head l2) (merge (tail l1) (tail l2))).
(** Another example is to merge three [inf_list]'s in a round robin way. *)
CoFixpoint merge3 (l1 : inf_list) (l2 : inf_list) (l3 : inf_list) : inf_list :=
  inf_cons (head l1) (inf_cons (head l2) (inf_cons (head l3) (merge3 (tail l1) (tail l2) (tail l3)))).
(** The following is a more compact definition. *)
Reset merge3.
CoFixpoint merge3 (l1 : inf_list) (l2 : inf_list) (l3 : inf_list) : inf_list :=
  inf_cons (head l1) (merge3 l2 l3 (tail l1)).
(** Using this definition we can define the following merge function which takes two elements of the
   first [inf_list] for every one element in the second. This was proposed as an exercise in Jacobs:1997
   (page 10).  They give no indication of what order we choose the elements from the first list or
   weather or not they should repeat.  In the footnote they suggest using [merge3], but this results
   in repeats if we maintain the order of the first. Here is the first definition. *)
CoFixpoint merge_2_1 (l1 : inf_list) (l2 : inf_list) : inf_list := merge3 l1 (tail l1) l2.
Reset merge_2_1.
(** We can get around the repeats with this definition if we do not maintain the order of
    the first list. *)
CoFixpoint merge_2_1 (l1 : inf_list) (l2 : inf_list) : inf_list := merge3 l1 (tail (tail l1)) l2.
Reset merge_2_1.
(** The following definition maintains the order of the first list and does not repeat, but it does
    not have as elegant of a solution as the previous ones. *)
CoFixpoint merge_2_1 (l1 : inf_list) (l2 : inf_list) : inf_list :=
  inf_cons (head l1) (inf_cons (head (tail l1)) (inf_cons (head l2) (merge_2_1 (tail (tail l1)) (tail l2)))).
End Inf_List.
