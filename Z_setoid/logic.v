Lemma contrapositive: forall P Q: Prop, (P -> Q) -> (~Q -> ~P).
Proof.
  intros. unfold not. intros. apply H in H1. contradiction.
Qed.

Lemma negb_true: forall b: bool, b = false <-> negb b = true.
Proof. intros; split; intros. rewrite H. reflexivity. destruct b. inversion H. reflexivity.
Defined.
