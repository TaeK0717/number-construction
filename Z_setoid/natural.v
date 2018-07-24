Require Import Coq.omega.Omega.

Lemma N_eq_plus_cons: forall a b c: nat, a = b <-> c + a = c + b.
Proof.
  split. intros. rewrite H. reflexivity.
  induction c.
  - simpl. intros. apply H.
  - simpl. intros. inversion H.
    apply IHc in H1. apply H1.
Qed.

Lemma N_lt_plus_cons: forall a b c: nat, a < b <-> c + a < c + b.
Proof.
  split. intros. omega.
  induction c.
  - simpl. intros. apply H.
  - simpl. intros. omega.
Qed.

Lemma N_eq_dec: forall a b: nat, a = b \/ a <> b.
Proof.
  intros. omega.
Qed.

Lemma N_trichotomy_diff: forall a b: nat, a <> b <-> a > b \/ a < b.
Proof. induction a.
  intros. split. intros. right. destruct b. contradiction. omega.
  intros. destruct H. inversion H. destruct b; omega.
  intros. destruct b. split. intros. left. omega. intros. destruct H. easy. omega.
  assert (S a <> S b <-> a <> b). omega.
  assert (S a > S b <-> a > b). omega.
  assert (S a < S b <-> a < b). omega.
  rewrite H, H0, H1. apply IHa.
Qed.

Lemma N_trichotomy: forall a b: nat, a > b \/ a = b \/ a < b.
Proof.
  intros.
  assert (a > b \/ a = b \/ a < b <-> a = b \/ (a > b \/ a < b)) by omega.
  rewrite H; clear H.
  rewrite <- N_trichotomy_diff.
  apply N_eq_dec.
Qed.

Lemma N_nonzero_minus: forall a b: nat, a > b <-> a - b <> 0.
Proof. intros. omega. Qed.

Lemma N_trichotomy_diff_minus: forall a b: nat, a <> b -> a - b <> 0 \/ b - a <> 0.
Proof.
  intros. repeat rewrite <- N_nonzero_minus. apply N_trichotomy_diff. apply H.
Qed.

Lemma N_S_inj: forall k l: nat, S k = S l -> k = l.
Proof. intros. omega. Qed.

Lemma N_S_surj: forall k l: nat, k = l -> S k = S l.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma N_minus_plus: forall n n0, n - n0 <> 0 -> (n - n0) + n0 = n.
Proof. intros. omega. Qed.

Lemma N_plus_minus: forall x y: nat, x + y - y = x.
Proof. intros. omega. Qed.

Lemma N_mult_n_Sm: forall a b: nat, a * S b = a + a * b.
Proof.
  intros. assert (S b = 1 + b) by reflexivity.
  rewrite H. rewrite mult_plus_distr_l. omega.
Qed.

Lemma N_mult_nonzero_inj: forall z x y: nat, S z * x = S z * y -> x = y.
Proof.
  induction z.
  - intros. omega.
  - induction x. simpl. destruct y.
    + reflexivity.
    + intros. rewrite <- mult_n_O in H. inversion H.
    + destruct y. intros. rewrite <- mult_n_O in H. inversion H.
      repeat rewrite (N_mult_n_Sm (S(S z)) _). intros.
      apply N_S_surj. apply IHx. omega.
Qed.

Lemma N_le__eq_lt: forall n m: nat, n <= m <-> n = m \/ n < m.
Proof. intros. omega. Qed.

Lemma N_not_le__gt: forall n m: nat, ~ n <= m <-> n > m.
Proof. intros. omega. Qed.

Lemma N_le_lt__lt: forall a b c d: nat, a <= b /\ c < d -> a + c < b + d.
Proof. intros. omega. Qed.

Lemma N_le_le__le: forall a b c d: nat, a <= b /\ c <= d -> a + c <= b + d.
Proof. intros. omega. Qed.

Lemma N_lt_mult_nonzero: forall a b c: nat, a < b -> a * S c < b * S c.
Proof.
  induction c.
  - omega.
  - intros. assert (a * S c < b * S c) by (apply IHc in H; apply H).
    repeat rewrite (N_mult_n_Sm _ (S c)).
    apply (N_le_lt__lt a b _ _). omega.
Qed.

Lemma N_rearr: forall a b c d: nat, a < b /\ c < d -> a * d + b * c < a * c + b * d.
Proof.
  induction b.
  - intros. destruct H. inversion H.
  - simpl in IHb. simpl. intros. simpl.
    destruct b. destruct H. inversion H. omega. inversion H2.
    assert (S (S b) - a <> 0). { destruct H. omega. }
    repeat rewrite (mult_comm (S b)). repeat rewrite <- N_mult_n_Sm.
    assert ((S (S b) - a) + a = S (S b)) by (apply N_minus_plus; apply H0).
    rewrite <- H1. repeat rewrite mult_plus_distr_l.
    rewrite (plus_comm _ (d * a)), (plus_comm _ (c * a)).
    repeat rewrite plus_assoc.
    rewrite (plus_comm _ (d * a)).
    rewrite (mult_comm a c), (mult_comm d a).
    apply N_lt_plus_cons. remember (S (S b) - a) as k.
    destruct k. contradiction.
    apply N_lt_mult_nonzero. destruct H. apply H2.
Qed.

Lemma N_leb_false: forall n m: nat, (n <=? m) = false <-> ~ (n <= m).
Proof.
  induction n;intro p;case p;simpl.
  split; intro. easy. omega. 
  intros; split; intro. discriminate. omega.
  split; intro. omega. reflexivity.
  intros; split; intro.
  apply IHn in H.
  omega.
  rewrite IHn.
  apply lt_not_le.
  omega.
Qed.

Lemma N_leb_false_gt: forall n m: nat, (n <=? m) = false <-> n > m.
Proof.
  intros.
  rewrite N_leb_false. omega.
Qed.

Lemma N_beq_false: forall n m: nat, (n =? m) = false <-> n <> m.
Proof.
  apply beq_nat_false_iff.
Qed.