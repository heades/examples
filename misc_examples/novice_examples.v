Lemma and_or_strange : (C -> P /\ ~A) -> ((P \/ ~A) -> B) -> C -> (A \/ B).
Proof.  
  intros H1 H2 H3.
  apply H1 in H3.
  destruct H3 as [H4 H3].
  apply or_intror with (A:=P) in H3.
  apply H2 in H3.
  apply or_intror with (A:=A) in H3.
  assumption.
Qed.

Lemma imp_strange : (P /\ R -> Q) -> (A -> B \/ C) -> (B -> P) -> (R <-> C) -> (C -> B) -> (A -> R) -> A -> Q.
Proof.
  intros H1 H2 H3 H4 H5 H9 H6.

  apply H1.
  split.
  apply H3.
  apply H5.
  destruct H4 as [H7 H8].
  apply H7.
  apply H9. assumption.

  apply H9; assumption.
Qed.
