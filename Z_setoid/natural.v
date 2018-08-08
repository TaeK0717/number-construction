Require Import Coq.omega.Omega.

(** 1. Simple things *)
Lemma N_S_bij: forall a b: nat, a = b <-> S a = S b.
Proof. split; omega. Defined.
Lemma N_nonzero__pos: forall a: nat, a <> 0 <-> a > 0.
Proof. split; omega. Defined.
Lemma N_lt__gt: forall a b: nat, a < b <-> b > a.
Proof. split; omega. Defined.
Lemma N_le__ge: forall a b: nat, a <= b <-> b >= a.
Proof. split; omega. Defined.
Lemma N_minus_zero: forall a: nat, a - 0 = a.
Proof. intros; omega. Defined.
Lemma N_minus_itself: forall a: nat, a - a = 0.
Proof. intros; omega. Defined.

(** 2. Trichotomy-like *)
Lemma N_eq_dec: forall a b: nat, a = b \/ a <> b.
Proof. intros; omega. Defined.
Lemma N_trichotomy_ne: forall a b: nat, a <> b <-> a < b \/ a > b.
Proof. intros; omega. Defined.
Lemma N_trichotomy: forall a b: nat, a < b \/ a = b \/ a > b.
Proof. intros; omega. Defined.
Lemma N_le__lt_eq: forall a b: nat, a <= b <-> a < b \/ a = b.
Proof. intros; omega. Defined.
Lemma N_lt__le_ne: forall a b: nat, a < b <-> a <= b /\ a <> b.
Proof. intros; omega. Defined.
Lemma N_nle__gt: forall a b: nat, ~ a <= b <-> a > b.
Proof. intros; omega. Defined.
Lemma N_nlt__ge: forall a b: nat, ~ a < b <-> a >= b.
Proof. intros; omega. Defined.
Lemma N_eq__le_ge: forall a b: nat, a = b <-> a <= b /\ a >= b.
Proof. intros; omega. Defined.

(** 3. Iff-conditions of inequalities *)
Lemma N_leb_true__le: forall a b: nat, (a <=? b) = true <-> a <= b.
Proof. apply Nat.leb_le. Defined.
Lemma N_ltb_true__lt: forall a b: nat, (a <? b) = true <-> a < b.
Proof. apply Nat.ltb_lt. Defined.
Lemma N_eqb_true__eq: forall a b: nat, (a =? b) = true <-> a = b.
Proof. apply Nat.eqb_eq. Defined.
Lemma N_leb_false__gt: forall a b: nat, (a <=? b) = false <-> a > b.
Proof.
  induction a; intro b; destruct b; simpl;
  split; intro; try easy; try omega.
  apply IHa in H; omega.
  rewrite IHa. omega.
Defined.
Lemma N_ltb_false__ge: forall a b: nat, (a <? b) = false <-> a >= b.
Proof.
  induction a; intro b; destruct b; simpl;
  split; intro; try easy; try omega.
  apply IHa in H; omega.
  unfold Nat.ltb; rewrite N_leb_false__gt; unfold gt, lt; omega.
Defined.
Lemma N_eqb_false__ne: forall a b: nat, (a =? b) = false <-> a <> b.
Proof. apply beq_nat_false_iff. Defined.
Lemma N_gt__pos_minus: forall a b: nat, a > b <-> a - b > 0.
Proof. intros; omega. Defined.
Lemma N_le__zero_minus: forall a b: nat, a <= b <-> a - b = 0.
Proof. intros; omega. Defined.

Ltac zero := simpl; repeat rewrite <- mult_n_O; repeat rewrite <- plus_n_O; repeat rewrite N_minus_zero; repeat rewrite N_minus_itself; try reflexivity.
Ltac zero_in H := simpl in H; repeat rewrite <- mult_n_O in H; repeat rewrite <- plus_n_O in H; repeat rewrite N_minus_zero in H; repeat rewrite N_minus_itself in H; try reflexivity.

Ltac one:= repeat rewrite mult_1_r.
Ltac one_in H:= repeat rewrite mult_1_r in H.

(** 4. Consistencies of inequalities *)
(* Use left operations *)
Lemma N_plus_minus: forall a b: nat, a + b - b = a.
Proof. intros; omega. Defined.
Lemma N_minus_plus: forall a b: nat, a >= b -> a - b + b = a.
Proof. intros; omega. Defined.
Lemma N_minus_distr: forall a b c: nat, a - b - c = a - (b + c).
Proof. intros; omega. Defined.
Lemma N_plus_minus_diff: forall a b c: nat, b >= c -> a + b - c = a + (b - c).
Proof. intros; omega. Defined.
Lemma N_minus_plus_distr: forall a b c: nat, a >= b -> b >= c -> a - b + c = a - (b - c).
Proof. intros. omega. Defined.
Lemma N_plus_minus_distr: forall a b c: nat, a + c >= b -> b >= c -> a + c - b = a - (b - c).
Proof. intros; omega. Defined.
Lemma N_cons_eq_plus: forall a b c: nat, b = c <-> a + b = a + c.
Proof. intros; omega. Defined.
Lemma N_cons_lt_plus: forall a b c: nat, b < c <-> a + b < a + c.
Proof. intros; omega. Defined.
Lemma N_cons_le_plus: forall a b c: nat, b <= c <-> a + b <= a + c.
Proof. intros; omega. Defined.
Lemma N_cons_eq_mult_pos: forall a b c: nat, a > 0 -> b = c <-> a * b = a * c.
Proof.
  destruct a. intros; easy. intros b c H. clear H.
  generalize dependent c. generalize dependent b. induction a.
  - intros. omega.
  - induction b. simpl. destruct c.
    + zero.
    + split; zero; intros; inversion H.
    + split. intros; rewrite H; reflexivity.
      destruct c. intros. rewrite <- mult_n_O in H. inversion H.
      assert (forall n: nat, S n = 1 + n) by reflexivity.
      rewrite (H b), (H c). repeat rewrite mult_plus_distr_l.
      repeat rewrite <- N_cons_eq_plus. apply IHb.
Defined.
Lemma N_cons_lt_mult_pos: forall a b c: nat, a > 0 -> b < c <-> a * b < a * c.
Proof.
  destruct a. intros; easy. intros b c H. clear H.
  generalize dependent c. generalize dependent b. induction a.
  - intros. omega.
  - induction b. simpl. destruct c.
    + zero.
    + split; zero; intros; apply gt_Sn_O.
    + split. intros. pose proof H as N.
      rewrite N_lt__le_ne in H. destruct H. clear H0.
      pose proof ((N_minus_plus c (S b)) H) as F. rewrite <- F.
      rewrite mult_plus_distr_l, plus_comm.
      remember (S (S a) * S b + S (S a) * (c - S b)) as f.
      assert (S (S a) * S b = S (S a) * S b + 0) by omega.
      rewrite H0; clear H0. rewrite Heqf; clear Heqf.
      rewrite <- N_cons_lt_plus. rewrite N_lt__gt, N_gt__pos_minus in N.
      remember (c - S b) as g. destruct g. easy. apply gt_Sn_O.
      destruct c. zero. intros. inversion H.
      assert (forall n: nat, S n = 1 + n) by reflexivity.
      rewrite (H b), (H c). repeat rewrite mult_plus_distr_l.
      repeat rewrite <- N_cons_lt_plus. apply IHb.
Defined.
Lemma N_cons_le_mult_pos: forall a b c: nat, a > 0 -> b <= c <-> a * b <= a * c.
Proof.
  destruct a. intros; easy. intros b c H.
  repeat rewrite N_le__lt_eq.
  rewrite (N_cons_lt_mult_pos (S a) b c).
  rewrite (N_cons_eq_mult_pos (S a) b c).
  reflexivity. apply H. apply H.
Defined.
Lemma N_rearrange: forall a b c d: nat, a < b -> c < d -> a * d + b * c < a * c + b * d.
Proof.
  induction b.
  - intros. inversion H.
  - simpl in IHb. simpl. intros. simpl.
    destruct b. inversion H. omega. inversion H2.
    assert (S (S b) - a > 0). { omega. }
    repeat rewrite (mult_comm (S b)).
    assert ((S (S b) - a) + a = S (S b)) by (apply N_minus_plus; omega).
    assert (forall n: nat, n + n * (S b) = n * S (S b)).
    { intros. assert (S (S b) = 1 + S b) by reflexivity. rewrite H3, mult_plus_distr_l. omega. }
    repeat rewrite H3. rewrite <- H2. repeat rewrite mult_plus_distr_l.
    rewrite (plus_comm _ (c * a)), (plus_comm _ (d * a)).
    repeat rewrite plus_assoc. rewrite (mult_comm d a), (mult_comm a c), (plus_comm (a * d) (c * a)),
    <- N_cons_lt_plus. repeat rewrite (mult_comm _ (S (S b) - a)). apply N_cons_lt_mult_pos.
    apply H1. apply H0.
Defined.
