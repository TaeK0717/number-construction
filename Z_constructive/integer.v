Require Import Coq.omega.Omega.
Require Import natural.
Require Import logic.

Delimit Scope int_scope with int.
Open Scope int_scope.

Inductive int: Type :=
| Z_pos: nat -> int
| Z_neg: nat -> int.

Coercion Z_pos : nat >-> int.

Definition Z_plus (z w: int) :=
match z with
| Z_pos n =>
  match w with
  | Z_pos m => Z_pos (n + m)
  | Z_neg m => if m <? n then n - (S m) else Z_neg (m - n)
  end
| Z_neg n =>
  match w with
  | Z_pos m => if n <? m then m - (S n) else Z_neg (n - m)
  | Z_neg m => Z_neg (S n + m)
  end
end.

Notation "z '+' w" := (Z_plus z w) (at level 50, left associativity) : int_scope.
Notation "z '+Z' w" := (Z_plus z w) (at level 50, left associativity) : type_scope.

(** negation of an integer: z |-> -z *)
Definition Z_opp (z: int): int :=
match z with
| Z_pos n => if n =? 0 then 0 else Z_neg (pred n)
| Z_neg n => (S n)
end.

Notation "'-' z" := (Z_opp z) (at level 35, right associativity) : int_scope.
Notation "'-Z' z" := (Z_opp z) (at level 35, right associativity) : type_scope.

(** subtraction *)
Definition Z_minus (z w: int) := z + - w.

Notation "z '-' w" := (Z_minus z w) (at level 50, left associativity) : int_scope.
Notation "z '-Z' w" := (Z_minus z w) (at level 50, left associativity) : type_scope.

(** multiplication *)
Definition Z_mult (z w: int): int :=
match z with
| Z_pos n =>
  match w with
  | Z_pos m => n * m
  | Z_neg m => Z_neg (n * m + n - 1)
  end
| Z_neg n =>
  match w with
  | Z_pos m => Z_neg (n * m + m - 1)
  | Z_neg m => (S n) * (S m)
  end
end.

Notation "z '*' w" := (Z_mult z w) (at level 40, left associativity) : int_scope.
Notation "z '*Z' w" := (Z_mult z w) (at level 40, left associativity) : type_scope.

(** zero and one *)
Notation "'0'" := (0, 0) : int_scope.
Notation "'Z0'" := (0, 0) : type_scope.
Notation "'1'" := (1, 0) : int_scope.
Notation "'Z1'" := (1, 0) : type_scope.

(** plus_assoc *)
Theorem Z_1: forall x y z: int, (x + y) + z = x + (y + z).
Proof. destruct x, y, z.
  simpl. rewrite plus_assoc. reflexivity.
  simpl. 
  simpl. simpl_relation. Qed.

(** plus_comm *)
Theorem Z_2: forall x y: int, x + y = y + x.
Proof. destruct x, y. simpl. simpl_relation. Qed.

(** zero as an identity for plus *)
Theorem Z_3: forall x: int, x + 0 = x.
Proof. destruct x. simpl. simpl_relation. Qed.

(** inverse element for plus *)
Theorem Z_4: forall x: int, x + - x = 0.
Proof. destruct x. unfold Z_eq. simpl_relation. Qed.

(** mult_assoc *)
Theorem Z_5: forall x y z: int, (x * y) * z = x * (y * z).
Proof. destruct x, y, z. simpl.
  repeat rewrite mult_plus_distr_l. repeat rewrite mult_plus_distr_r. repeat rewrite plus_assoc. repeat rewrite mult_assoc. omega.
Qed.

(** mult_comm *)
Theorem Z_6: forall x y: int, x * y = y * x.
Proof. destruct x, y. simpl. repeat rewrite plus_assoc.
rewrite (mult_comm n1 n), (mult_comm n0 n2), (mult_comm n1 n0), (mult_comm n n2). omega. Qed.

(** one as an identity for mult *)
Theorem Z_7: forall x: int, x * 1 = x.
Proof. destruct x. simpl. omega. Qed.

(** left distribution law *)
Theorem Z_8: forall x y z: int, x * (y + z) = x * y + x * z.
Proof. destruct x, y, z. simpl.
  repeat rewrite mult_plus_distr_l. repeat rewrite mult_plus_distr_r. repeat rewrite plus_assoc. repeat rewrite mult_assoc. omega. Qed.

(** Z is an integral domain *)
Theorem Z_9: forall x y: int, x * y = 0 -> x = 0 \/ y = 0.
Proof. destruct x. remember (beq_nat n n0) as b. destruct b.
  - intros. left. symmetry in Heqb.
    rewrite beq_nat_true_iff in Heqb. rewrite Heqb. simpl. reflexivity.
  - intros. right. symmetry in Heqb.
    rewrite beq_nat_false_iff in Heqb. simpl in H.
    destruct y. simpl in H. repeat (rewrite <- plus_n_O in H).
    simpl. repeat (rewrite <- plus_n_O).

    Close Scope int_scope.

    apply N_trichotomy_diff in Heqb.
    assert (forall q r: nat, q - r <> 0 /\ q * n1 + r * n2 = q * n2 + r * n1 -> n1 = n2).
    { intros. destruct H0.
      assert (q * n1 - r * n1 = q * n2 - r * n2). { omega. }
      rewrite <- (N_minus_plus q r) in H2.
      repeat rewrite mult_plus_distr_r in H2.
      repeat rewrite N_plus_minus in H2.
      remember (q - r) as k. destruct k. omega. apply (N_mult_nonzero_inj k).
      apply H2. apply H0.
    }
    destruct Heqb.
    apply (H0 n n0). split. rewrite N_trichotomy_diff. left. omega. apply H.
    apply (H0 n0 n). split. rewrite N_trichotomy_diff. left. omega. omega.
    Open Scope int_scope.
Qed.

(** natural order for Z *)
Definition Z_le (x y: int) := (** x <= y iff *)
match x with
| (a1, a2) =>
  match y with
  | (b1, b2) => (a1 + b2 <= b1 + a2)
  end
end.

Add Morphism Z_le with signature Z_eq ==> Z_eq ==> iff as Z_le_morph.
Proof.
  destruct x, y, x0, y0.
  unfold Z_eq in H. unfold Z_eq. unfold iff. unfold Z_le.
  intros. split; omega.
Qed.

Notation "z '<=Z' w" := (Z_le z w) (at level 70, no associativity) : type_scope.
Notation "z '<Z' w" := (~ Z_le w z) (at level 70, no associativity) : type_scope.
Notation "z '>=Z' w" := (Z_le w z) (at level 70, no associativity) : type_scope.
Notation "z '>Z' w" := (~ Z_le z w) (at level 70, no associativity) : type_scope.

Theorem Z_le_refl: subrelation Z_le Z_le.
Proof. unfold subrelation. destruct x, y. unfold Z_le. intros. apply H. Qed.

Lemma Z_neg_diff__lt: forall x y: int, x - y <Z 0 <-> x <Z y.
  Proof. intros. destruct x, y. split; unfold Z_le; simpl; omega. Qed.
Lemma Z_no_diff__eq: forall x y: int, x - y = 0 <-> x = y.
  Proof. intros. destruct x, y. split; unfold Z_le; simpl; omega. Qed.
Lemma Z_pos_diff__gt: forall x y: int, x - y >Z 0 <-> x >Z y.
  Proof. intros. destruct x, y. split; unfold Z_le; simpl; omega. Qed.

Lemma Z_10_0: forall x: int,
    (  x <Z 0 /\ ~ x = 0 /\ ~ x >Z 0) \/
    (~ x <Z 0 /\   x = 0 /\ ~ x >Z 0) \/
    (~ x <Z 0 /\ ~ x = 0 /\   x >Z 0).
Proof.
  destruct x. remember (n - n0)%nat as d1. destruct d1.
  - remember (n0 - n)%nat as d2. destruct d2.
    + right. left. split.
      unfold Z_le. simpl. omega.
      split; [| unfold Z_le]; simpl; omega.
    + left. split.
      unfold Z_le. simpl. omega.
      split; [unfold not | unfold Z_le]; simpl; omega.
  - right. right. split.
    unfold Z_le. simpl. omega.
    split; [unfold not | unfold Z_le]; simpl; omega.
Qed.

(** trichotomy *)
Theorem Z_10: forall x y: int,
  (  x <Z y /\ ~ x = y /\ ~ x >Z y) \/
  (~ x <Z y /\   x = y /\ ~ x >Z y) \/
  (~ x <Z y /\ ~ x = y /\   x >Z y).
Proof.
  intros. rewrite <- Z_neg_diff__lt. rewrite <- Z_no_diff__eq. rewrite <- (Z_pos_diff__gt x y).
  apply Z_10_0.
Qed.

(** trichotomy *)
Corollary Z_10_1: forall x y: int, x <Z y \/ x = y \/ x >Z y.
Proof.
  intros.
  pose proof (Z_10 x y).
  destruct H; destruct H.
  - left. apply H.
  - destruct H. destruct H0. right. left. apply H0.
  - destruct H. destruct H0. right. right. apply H1.
Qed.

(** transitivity *)
Theorem Z_11: forall x y z: int, x <Z y /\ y <Z z -> x <Z z.
Proof. intros x y z. rewrite <- (Z_neg_diff__lt x y). rewrite <- (Z_neg_diff__lt x z). rewrite <- (Z_neg_diff__lt y z).
  assert (forall a b: int, a <Z 0 /\ b <Z 0 -> a + b <Z 0).
  { destruct a, b. intros. simpl in H; destruct H. simpl. omega. }
  assert ((x - y) + (y - z) = x - z).
  { destruct x, y, z. simpl. omega. }
  intros. rewrite <- H0. apply (H (x - y) (y - z)). apply H1. Qed.

(** addition preserves the order *)
Theorem Z_12: forall x y z: int, x <Z y -> x + z <Z y + z.
Proof. intros x y z. rewrite <- Z_pos_diff__gt. destruct x, y, z. simpl. omega. Qed.

(** mult by positive number preserves the order *)
Theorem Z_13: forall x y z: int, x <Z y /\ z >Z 0 -> x * z <Z y * z.
Proof.
  intros x y z. rewrite <- Z_pos_diff__gt. rewrite <- (Z_pos_diff__gt (y * z) _).
  assert (forall a b: int, a >Z 0 /\ b >Z 0 -> a * b >Z 0).
  { destruct a, b. simpl. repeat rewrite <- plus_n_O.
    repeat rewrite N_not_le__gt.
    rewrite (plus_comm (n * n1) _), (plus_comm (n * n2) _).
    apply (N_rearr n0 n n2 n1). }
  assert (forall v w: int, v + - w = v - w).
  { destruct v, w. simpl. omega. }
  assert (forall v w: int, v * - w = - (v * w)).
  { destruct v, w. simpl. omega. }
  assert (y * z - x * z = (y - x) * z).
  { rewrite (Z_6 y z), (Z_6 x z), (Z_6 _ z).
    repeat rewrite <- H0. symmetry. rewrite <- H1. apply Z_8. }
  rewrite H2. apply H.
Qed.

(** Z is not a trivial ring *)
Theorem Z_14: 0 <Z> 1.
Proof. unfold not. unfold Z_eq. simpl. intros. inversion H. Qed.

Lemma Z_not_not_equal: forall z w: int, z = w <-> ~ z <Z> w.
Proof.
  split.
    - intros. unfold not. intros. apply H0 in H. contradiction.
    - intros. unfold not in H. destruct z, w. unfold Z_eq in H.
      remember (beq_nat (n + n2) (n0 + n1)) as b.
      destruct b.
      + symmetry in Heqb. apply beq_nat_true_iff in Heqb. simpl. auto.
      + symmetry in Heqb. apply beq_nat_false_iff in Heqb. apply H in Heqb. inversion Heqb.
Qed.

Lemma Z_mult_0: forall z: int, z * 0 = 0.
Proof.
  destruct z. simpl. omega.
Qed.

Lemma Z_mult_neg_1: forall z: int, - z = (0, 1) * z.
Proof.
  destruct z. simpl. omega.
Qed.

Lemma Z_le_inv: forall z w: int, z <=Z w <-> - z >=Z - w.
Proof.
  destruct z, w. simpl. omega.
Qed.

Lemma Z_eq_mult_cons: forall a b c: int, c <Z> 0 -> a = b <-> c * a = c * b.
Proof.
  intros.
  assert (forall z w: int, z <Z> w <-> z >Z w \/ z <Z w).
  { split. assert (
      (  z <Z w /\ ~ z = w /\ ~ z >Z w) \/
      (~ z <Z w /\   z = w /\ ~ z >Z w) \/
      (~ z <Z w /\ ~ z = w /\   z >Z w)
    ). { apply Z_10. }
    destruct H0.
      - right. destruct H0. apply H0.
      - destruct H0. destruct H0. destruct H1. contradiction.
                     destruct H0. destruct H1. left. apply H2.
      - intros. destruct H0; destruct z, w; unfold Z_eq; unfold Z_le in H0; omega.
  }
  split.
  intros. rewrite H1. reflexivity.
  rewrite (Z_not_not_equal a b), (Z_not_not_equal (c * a) (c * b)).
  apply contrapositive. repeat (rewrite H0). rewrite H0 in H.
  assert (forall z: int, z <Z 0 <-> - z >Z 0).
  { destruct z. unfold Z_le, Z_neg. omega. }
  assert (forall z: int, - - z = z).
  { destruct z. unfold Z_eq, Z_neg. omega. }
  intros. destruct H. destruct H3.
  - left. repeat rewrite (Z_6 c _). apply Z_13. auto.
  - right. repeat rewrite (Z_6 c _). apply Z_13. auto.
  - remember (- c) as d.
    assert (c = - d). { rewrite Heqd. symmetry. apply H2. }
    rewrite H4 in H. apply H1 in H. rewrite H2 in H.
    repeat rewrite H4. repeat rewrite (Z_mult_neg_1 d).
    repeat rewrite Z_5. repeat rewrite <- Z_mult_neg_1.
    repeat rewrite <- H1. repeat rewrite <- Z_le_inv.
    destruct H3. right. repeat rewrite (Z_6 d _). apply Z_13. auto.
    left. repeat rewrite (Z_6 d _). apply Z_13. auto.
Qed.

Close Scope int_scope.
