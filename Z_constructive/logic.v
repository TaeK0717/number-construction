Lemma contrapositive: forall P Q: Prop, (P -> Q) -> (~Q -> ~P).
Proof.
  intros. unfold not. intros. apply H in H1. contradiction.
Qed.