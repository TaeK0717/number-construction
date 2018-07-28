Require Import Coq.omega.Omega.
Require Import natural.
Require Import logic.

Delimit Scope int_scope with int.
Open Scope int_scope.

Inductive int: Type :=
| Z_pos: nat -> int
| Z_neg: nat -> int.

Definition Z_plus (z w: int) :=
match z, w with
| Z_pos n, Z_pos m => Z_pos (n + m)
| Z_pos n, Z_neg m => if m <? n then Z_pos (n - (S m)) else Z_neg (m - n)
| Z_neg n, Z_pos m => if n <? m then Z_pos (m - (S n)) else Z_neg (n - m)
| Z_neg n, Z_neg m => Z_neg (S n + m)
end.

Notation "z '+' w" := (Z_plus z w) (at level 50, left associativity) : int_scope.
Notation "z '+Z' w" := (Z_plus z w) (at level 50, left associativity) : type_scope.

(** negation of an integer: z |-> -z *)
Definition Z_opp (z: int): int :=
match z with
| Z_pos n => if n =? 0 then Z_pos 0 else Z_neg (pred n)
| Z_neg n => Z_pos (S n)
end.

Notation "'-' z" := (Z_opp z) (at level 35, right associativity) : int_scope.
Notation "'-Z' z" := (Z_opp z) (at level 35, right associativity) : type_scope.

(** subtraction *)
Definition Z_minus (z w: int) := z + - w.

Notation "z '-' w" := (Z_minus z w) (at level 50, left associativity) : int_scope.
Notation "z '-Z' w" := (Z_minus z w) (at level 50, left associativity) : type_scope.

(** multiplication *)
Definition Z_mult (z w: int): int :=
match z, w with
  | Z_pos n, Z_pos m => Z_pos (n * m)
  | Z_pos n, Z_neg m => - Z_pos (n * (S m))
  | Z_neg n, Z_pos m => - Z_pos ((S n) * m)
  | Z_neg n, Z_neg m => Z_pos ((S n) * (S m))
end.

Notation "z '*' w" := (Z_mult z w) (at level 40, left associativity) : int_scope.
Notation "z '*Z' w" := (Z_mult z w) (at level 40, left associativity) : type_scope.

(** plus_assoc *)
Theorem Z_1: forall x y z: int, (x + y) + z = x + (y + z).
Proof. destruct x, y, z.
  (* CASE 1 *)
  simpl. rewrite plus_assoc. reflexivity.

  (* CASE 2 *)
  simpl. remember (n1 <? n0) as b; destruct b; symmetry in Heqb.
    (* n1 < n0 *)
    rewrite N_ltb_true__lt in Heqb.
    assert (n1 < n + n0) by omega.
    rewrite <- N_ltb_true__lt in H.
    rewrite H. unfold lt in Heqb.
    apply (N_minus_plus n0 (S n1)) in Heqb.
    remember (n0 - (S n1))%nat as k.
    rewrite <- Heqb. repeat rewrite plus_assoc.
    rewrite N_plus_minus.
    reflexivity.

    (* n1 >= n0 *)
    rewrite N_ltb_false__ge in Heqb.
    remember (n1 <? n + n0) as c; destruct c; symmetry in Heqc.
      (* n1 < n + n0 *)
      rewrite N_ltb_true__lt in Heqc.
      apply N_minus_plus in Heqb.
      remember (n1 - n0)%nat as k.
      rewrite <- Heqb in Heqc; repeat rewrite (plus_comm _ n0) in Heqc.
      rewrite <- N_cons_lt_plus in Heqc.
      rewrite <- N_ltb_true__lt in Heqc.
      rewrite Heqc. rewrite <- Heqb.
      assert (Tmp: S (k + n0)%nat = (n0 + (S k))%nat) by omega.
      rewrite Tmp. rewrite <- N_minus_distr, N_plus_minus. reflexivity.

      (* n1 >= n + n0 *)
      rewrite N_ltb_false__ge in Heqc.
      apply N_minus_plus in Heqb.
      remember (n1 - n0)%nat as k.
      rewrite <- Heqb in Heqc; repeat rewrite (plus_comm _ n0) in Heqc.
      unfold ge in Heqc. rewrite <- N_cons_le_plus in Heqc.
      rewrite N_le__ge, <- N_ltb_false__ge in Heqc.
      rewrite Heqc, <- Heqb.
      rewrite (plus_comm n n0), <- N_minus_distr, N_plus_minus. reflexivity.

  (* CASE 3 *)
  simpl. remember (n0 <? n) as b; remember (n0 <? n1) as c;
  destruct b, c; symmetry in Heqb, Heqc.
    (* n0 < n /\ n0 < n1 *)
    rewrite N_ltb_true__lt in Heqb, Heqc.
    unfold lt in Heqb, Heqc. unfold Z_plus.
    rewrite (plus_comm _ n1). rewrite <- N_plus_minus_diff.
    rewrite (plus_comm n1 n). rewrite N_plus_minus_diff. reflexivity.
    apply Heqc. apply Heqb.

    (* n0 < n /\ n0 >= n1 *)
    rewrite N_ltb_true__lt in Heqb; rewrite N_ltb_false__ge in Heqc.
    unfold Z_plus. assert (n0 - n1 < n) by omega. rewrite <- N_ltb_true__lt in H.
    rewrite H. assert (S (n0 - n1) = ((S n0) - n1)%nat) by omega.
    rewrite H0. rewrite N_minus_plus_distr. reflexivity.
    apply Heqb. apply le_S. apply Heqc.

    (* n0 >= n /\ n0 < n1 *)
    unfold Z_plus.
    rewrite N_ltb_true__lt in Heqc.
    rewrite N_ltb_false__ge in Heqb.
    assert (n0 - n < n1) by omega.
    rewrite <- N_ltb_true__lt in H.
    rewrite H. assert (S (n0 - n) = ((S n0) - n)%nat) by omega.
    rewrite H0. rewrite <- N_minus_plus_distr. rewrite plus_comm. reflexivity.
    apply Heqc. apply le_S; apply Heqb.

    (* n0 >= n /\ n0 >= n1 *)
    remember (n0 - n1 <? n) as d; destruct d; symmetry in Heqd; unfold Z_plus;
    rewrite N_ltb_false__ge in Heqb, Heqc.
      (* n0 >= n /\ n0 >= n1 /\ n0 - n1 < n *)
      rewrite N_ltb_true__lt in Heqd.
      assert (n0 - n < n1) by omega.
      rewrite <- N_ltb_true__lt in H.
      rewrite H.
      assert (forall a b: nat, a >= b -> S (a - b)%nat = ((S a) - b)%nat) by (intros; omega).
      repeat rewrite H0.
      rewrite <- N_plus_minus_distr.
      rewrite <- N_plus_minus_distr.
      pose proof ((N_minus_plus n0 n1) Heqc) as PM.
      pose proof ((N_minus_plus n0 n) Heqb) as PM1.
      rewrite (plus_comm n1 n). reflexivity.
      omega. omega. omega. omega. omega. omega.

      (* n0 >= n /\ n0 >= n1 /\ n0 - n1 >= n *)
      rewrite N_ltb_false__ge in Heqd.
      assert (n0 - n >= n1) by omega.
      rewrite <- N_ltb_false__ge in H.
      rewrite H.
      repeat rewrite N_minus_distr.
      rewrite (plus_comm n n1). reflexivity.

  (* CASE 4 *)
  simpl. remember (n0 <? n) as b; destruct b; simpl; unfold Z_plus; symmetry in Heqb.
    (* n0 < n *)
    rewrite N_ltb_true__lt in Heqb.
    remember (S (n0 + n1) <? n) as c; destruct c; simpl; symmetry in Heqc.
      (* n0 < n /\ S (n0 + n1) < n *)
      rewrite N_ltb_true__lt in Heqc.
      assert (n1 < n - S n0) by omega.
      rewrite <- N_ltb_true__lt in H.
      rewrite H.
      rewrite N_minus_distr.
      rewrite <- plus_n_Sm. reflexivity.

      (* n0 < n /\ S (n0 + n1) >= n *)
      rewrite N_ltb_false__ge in Heqc.
      assert (n1 >= n - S n0) by omega.
      rewrite <- N_ltb_false__ge in H.
      rewrite H.
      destruct n. inversion Heqb.
      assert ((S n - S n0)%nat = (n - n0)%nat) by omega.
      rewrite H0. repeat rewrite <- N_plus_minus_distr.
      rewrite (plus_comm n1 n0). reflexivity.
      omega. omega.

    (* n0 >= n *)
    rewrite N_ltb_false__ge in Heqb.
    assert (S (n0 + n1) >= n) by omega.
    rewrite <- N_ltb_false__ge in H.
    rewrite H.
    destruct n. assert ((n0 - 0)%nat = n0) by omega. rewrite H0. reflexivity.
    assert (S (n0 - S n + n1) = (n0 + n1 - n)%nat).
      apply (N_minus_plus n0 (S n)) in Heqb.
      remember ((n0 - S n)%nat) as k.
      rewrite <- Heqb.
      rewrite <- plus_assoc.
      rewrite (plus_comm (S n)).
      rewrite plus_assoc.
      assert ((k + n1 + S n - n)%nat = S(k + n1)) by omega.
      rewrite H0. reflexivity.
    rewrite H0. reflexivity.

  (* CASE 5 *)
  simpl. remember (n <? n0) as b; destruct b; simpl; unfold Z_plus; symmetry in Heqb.
    (* n < n0 *)
    rewrite N_ltb_true__lt in Heqb.
    assert (n < n0 + n1) by omega.
    rewrite <- N_ltb_true__lt in H.
    rewrite H.
    rewrite (plus_comm n0 n1).
    rewrite N_plus_minus_diff.
    rewrite (plus_comm n1 _).
    reflexivity.
    apply Heqb.

    (* n >= n0 *)
    remember (n <? n0 + n1) as c; destruct c; simpl; symmetry in Heqc;
    rewrite N_ltb_false__ge in Heqb.
      (* n >= n0 /\ n < n0 + n1 *)
      rewrite N_ltb_true__lt in Heqc.
      assert (n - n0 < n1) by omega.
      rewrite <- N_ltb_true__lt in H.
      rewrite H.
      assert (S (n - n0) = (S n - n0)%nat) by omega.
      rewrite H0.
      rewrite <- N_plus_minus_distr.
      rewrite plus_comm.
      reflexivity.
      unfold ge; rewrite plus_comm.
      apply Heqc.
      apply le_S, Heqb.

      (* n >= n0 /\ n < n0 + n1 *)
      rewrite N_ltb_false__ge in Heqc.
      assert (n - n0 >= n1) by omega.
      rewrite <- N_ltb_false__ge in H.
      rewrite H.
      rewrite N_minus_distr.
      reflexivity.

  (* CASE 6 *)
  simpl. remember (n <? n0) as b; remember (n1 <? n0) as c;
  destruct b, c; symmetry in Heqb, Heqc.
    (* n < n0 /\ n1 < n0 *)
    rewrite N_ltb_true__lt in Heqb, Heqc.
    unfold lt in Heqb, Heqc. unfold Z_plus.
    remember (n1 <? n0 - S n) as d; destruct d; symmetry in Heqd; unfold Z_plus.
      (* n < n0 /\ n1 < n0 /\ n1 < n0 - S n *)
      rewrite N_ltb_true__lt in Heqd.
      assert (n < n0 - S n1) by omega.
      rewrite <- N_ltb_true__lt in H.
      rewrite H.
      repeat rewrite N_minus_distr.
      rewrite plus_comm. reflexivity.

      (* n < n0 /\ n1 < n0 /\ n1 >= n0 - S n *)
      rewrite N_ltb_false__ge in Heqd.
      assert (n >= n0 - S n1) by omega.
      rewrite <- N_ltb_false__ge in H.
      rewrite H.
      repeat rewrite <- N_plus_minus_distr.
      assert ((n1 + S n)%nat = (n + S n1)%nat) by omega.
      rewrite H0. reflexivity.
      omega. omega. omega. omega.

    (* n < n0 /\ n1 >= n0 *)
    rewrite N_ltb_true__lt in Heqb; rewrite N_ltb_false__ge in Heqc.
    unfold Z_plus. assert (n1 >= n0 - S n) by omega. rewrite <- N_ltb_false__ge in H.
    rewrite H.
    repeat rewrite <- N_plus_minus_distr.
    rewrite plus_comm. rewrite N_plus_minus_diff. reflexivity.
    omega. omega. omega.

    (* n >= n0 /\ n1 < n0 *)
    rewrite N_ltb_true__lt in Heqc.
    rewrite N_ltb_false__ge in Heqb.
    unfold Z_plus.
    assert (n >= n0 - S n1) by omega.
    rewrite <- N_ltb_false__ge in H.
    rewrite H. simpl. rewrite plus_n_Sm.
    rewrite <- N_minus_plus_distr. reflexivity.
    omega. omega.

    (* n >= n0 /\ n1 >= n0 *)
    unfold Z_plus; rewrite N_ltb_false__ge in Heqb, Heqc.
    assert ((S (n - n0) + n1)%nat = (S (n + (n1 - n0)))%nat) by omega.
    rewrite H. reflexivity.

  (* CASE 7 *)
  simpl. remember (S (n + n0) <? n1) as b; destruct b; symmetry in Heqb.
    (* S (n + n0) < n1 *)
    rewrite N_ltb_true__lt in Heqb.
    assert (n0 < n1) by omega.
    rewrite <- N_ltb_true__lt in H.
    rewrite H.
    assert (n < n1 - S n0) by omega.
    rewrite <- N_ltb_true__lt in H0.
    rewrite H0.
    rewrite N_minus_distr.
    rewrite plus_comm, plus_n_Sm.
    reflexivity.

    (* S (n + n0) >= n1 *)
    rewrite N_ltb_false__ge in Heqb.
    assert (n >= n1 - S n0) by omega.
    rewrite <- N_ltb_false__ge in H.
    remember (n0 <? n1) as c; destruct c; symmetry in Heqc.
      (* S (n + n0) >= n1 /\ n0 < n1 *)
      rewrite N_ltb_true__lt in Heqc.
      rewrite H.
      destruct n1.
      inversion Heqc.
      assert ((S n1 - S n0)%nat = (n1 - n0)%nat) by omega.
      rewrite H0; clear H0.
      rewrite <- N_plus_minus_distr.
      reflexivity.
      omega. omega.

      (* S (n + n0) >= n1 /\ n0 >= n1 *)
      rewrite N_ltb_false__ge in Heqc.
      destruct n1. assert ((n0 - 0)%nat = n0) by omega.
      rewrite H0. reflexivity.
      assert ((n + n0 - n1)%nat = (S n + n0 - S n1)%nat) by omega.
      rewrite H0. rewrite N_plus_minus_diff. reflexivity. omega.

  (* CASE 8 *)
  simpl. rewrite <- plus_assoc, (plus_n_Sm n). reflexivity.
Qed.

(** plus_comm *)
Theorem Z_2: forall x y: int, x + y = y + x.
Proof. destruct x, y.
  - simpl. rewrite (plus_comm n n0). reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite (plus_comm n n0). reflexivity.
Qed.

(** zero as an identity for plus *)
Theorem Z_3: forall x: int, x + Z_pos 0 = x.
Proof. destruct x.
  - simpl. rewrite plus_0_r. reflexivity.
  - simpl. assert ((n - 0)%nat%nat = n) by omega. rewrite H. reflexivity.
Qed.

(** inverse element for plus *)
Theorem Z_4: forall x: int, x + - x = Z_pos 0.
Proof. destruct x.
  - destruct n.
    + simpl. reflexivity.
    + simpl. assert (n < S n) by omega. rewrite <- N_ltb_true__lt in H.
      rewrite H. assert ((n - n)%nat%nat = 0) by omega. rewrite H0. reflexivity.
  - simpl. assert (n < S n) by omega. rewrite <- N_ltb_true__lt in H.
    rewrite H. assert ((n - n)%nat%nat = 0) by omega. rewrite H0. reflexivity.
Qed.

(** mult_assoc *)
Theorem Z_5: forall x y z: int, (x * y) * z = x * (y * z).
Proof.
  assert (L: forall n n0 n1: nat, (n1 + (n0 + n * S n0) * S n1)%nat
          = (n1 + n0 * S n1 + n * S (n1 + n0 * S n1))%nat).
    intros; simpl. assert (S (n1 + n0 * S n1) = ((S n0) * (S n1))%nat) by reflexivity.
    rewrite H. rewrite mult_plus_distr_r, plus_assoc, mult_assoc. reflexivity.

  destruct x, y, z; simpl.
  - rewrite mult_assoc. reflexivity.
  - destruct n0. zero.
    destruct n. zero. simpl.
    rewrite mult_plus_distr_r, <- mult_assoc, plus_assoc.
    reflexivity.
  - destruct n. zero. destruct (n1 + n0 * n1 =? 0); reflexivity.
    assert (((S n * S n0)%nat =? 0) = false) by reflexivity.
    rewrite H. destruct n1.
      zero. simpl. zero. simpl. rewrite <- L. reflexivity.
  - destruct n. zero. simpl. rewrite <- L. reflexivity.
  - destruct n0. zero.
    simpl. destruct n1. zero. simpl. rewrite L. reflexivity.
  - destruct n0. zero. simpl. rewrite L. reflexivity.
  - destruct n1. zero. simpl. zero. simpl. rewrite L. reflexivity.
  - rewrite L. reflexivity.
Qed.

(** mult_comm *)
Theorem Z_6: forall x y: int, x * y = y * x.
Proof. destruct x, y; simpl.
  - rewrite mult_comm. reflexivity.
  - destruct n. zero. rewrite (mult_comm (S n)). reflexivity.
  - destruct n0. zero. rewrite (mult_comm (S n0)). reflexivity.
  - assert (forall a b: nat, S (b + a * S b) = ((S a) * (S b))%nat) by reflexivity.
    repeat rewrite H. rewrite mult_comm. reflexivity.
Qed.

(** one as an identity for mult *)
Theorem Z_7: forall x: int, x * Z_pos 1 = x.
Proof. destruct x; simpl; assert ((n * 1)%nat = n%nat) by omega; rewrite H; reflexivity. Qed.

(** left distribution law *)
Theorem Z_8: forall x y z: int, x * (y + z) = x * y + x * z.
Proof. destruct x, y, z; simpl.
  - rewrite mult_plus_distr_l. reflexivity.
  - destruct n. zero. destruct (n1 <? n0); zero.
    simpl. assert (forall a b: nat, (b + a * b)%nat = ((S a) * b)%nat) by reflexivity.
    repeat rewrite H.
    assert ((n1 + n * S n1 <? S n * n0) = ((S n) * (S n1) <=? S n * n0)) by reflexivity.
    rewrite H0.
    pose proof (N_cons_le_mult_pos (S n) (S n1) n0) as F.
    assert (F1: S n > 0) by omega. apply F in F1.
    repeat rewrite <- N_leb_true__le in F1.
    remember (S n * S n1 <=? S n * n0) as b; destruct b.
    assert ((S n1 <=? n0) = true) by (rewrite F1; reflexivity).
    unfold Nat.ltb. rewrite H1. remember ((n0 - S n1)%nat) as k.
    rewrite H. assert (S (n1 + n * S n1) = ((S n) * (S n1))%nat).
      rewrite <- H. reflexivity.
    rewrite H2. rewrite <- (N_minus_plus n0 (S n1)).
    rewrite <- Heqk. rewrite mult_plus_distr_l.
    rewrite N_plus_minus. reflexivity. rewrite N_leb_true__le in H1. apply H1.
    assert ((S n1 <=? n0) = false).
      rewrite N_leb_true__le in F1.
      rewrite N_le__ge in F1.
      assert (false = true -> False) by discriminate.
      assert (n0 < S n1). rewrite N_lt__gt, <- N_nle__gt.
      pose proof (contrapositive (n0 >= S n1) (false = true)) as P.
      destruct F1.
      apply P in H2. apply H2. unfold not. apply H1.
      rewrite N_leb_false__gt. unfold gt. apply H2.
    rewrite N_leb_false__gt in H1. assert (n1 >= n0) by omega.
    rewrite <- N_ltb_false__ge in H2. rewrite H2.
    rewrite N_ltb_false__ge in H2. remember ((n1 - n0)%nat) as k.
    rewrite <- (N_minus_plus n1 n0). rewrite <- Heqk.
    assert (S (k + n0) = (S k + n0)%nat) by reflexivity.
    rewrite H3, mult_plus_distr_l.
    assert ((k + n0 + (n * S k + n * n0))%nat = (k + n * S k + (n0 + n * n0))%nat) by omega.
    rewrite H4. simpl. rewrite N_plus_minus. reflexivity. apply H2.


Admitted.

(** Z is an integral domain *)
Theorem Z_9: forall x y: int, x * y = Z_pos 0 -> x = Z_pos 0 \/ y = Z_pos 0.
Proof. Admitted.

(** natural order for Z *)
Definition Z_leb (z w: int): bool := (** x <=? y iff *)
match z, w with
  | Z_pos n, Z_pos m => n <=? m
  | Z_pos n, Z_neg m => false
  | Z_neg n, Z_pos m => true
  | Z_neg n, Z_neg m => m <=? n
end.


Notation "z '<=?Z' w" := (Z_leb z w) (at level 70, no associativity) : type_scope.
Notation "z '<?Z' w" := (negb Z_leb w z) (at level 70, no associativity) : type_scope.
Notation "z '>=?Z' w" := (Z_leb w z) (at level 70, no associativity) : type_scope.
Notation "z '>?Z' w" := (negb Z_leb z w) (at level 70, no associativity) : type_scope.

Definition Z_le (z w: int): Prop := (** x <=? y iff *)
match z, w with
  | Z_pos n, Z_pos m => n <= m
  | Z_pos n, Z_neg m => False
  | Z_neg n, Z_pos m => True
  | Z_neg n, Z_neg m => m <= n
end.

Notation "z '<=Z' w" := (Z_le z w) (at level 70, no associativity) : type_scope.
Notation "z '<Z' w" := (~ Z_le w z) (at level 70, no associativity) : type_scope.
Notation "z '>=Z' w" := (Z_le w z) (at level 70, no associativity) : type_scope.
Notation "z '>Z' w" := (~ Z_le z w) (at level 70, no associativity) : type_scope.

Lemma Z_neg_diff__lt: forall x y: int, x - y <Z Z_pos 0 <-> x <Z y.
Proof. assert (N: (0 =? 0) = true) by reflexivity.
  intros. destruct x, y; split; intros; unfold Z_le; simpl; simpl in H.
  - destruct n0. rewrite N in H.
    rewrite N_nle__gt in H. inversion H.
    assert ((S n0 =? 0) = false) by reflexivity. rewrite H0 in H. simpl in H.
    remember (n0 <? n) as b; destruct b.
    omega. symmetry in Heqb; rewrite N_ltb_false__ge in Heqb. omega.
  - destruct n0. rewrite N_nle__gt in H; inversion H.
    rewrite N_nle__gt in H. simpl. assert (n0 >= n) by omega.
    rewrite <- N_ltb_false__ge in H0. rewrite H0. easy.
  - rewrite N_nle__gt in H; inversion H.
  - easy.
  - easy.
  - destruct n0; simpl; apply H.
  - unfold not; intros. assert (n < S n0) by omega.
    rewrite <- N_ltb_true__lt in H1.
    rewrite H1 in H. omega.
  - assert (n >= S n0) by omega.
    rewrite <- N_ltb_false__ge in H0.
    rewrite H0. easy.
Qed.

Lemma Z_no_diff__eq: forall x y: int, x - y = Z_pos 0 <-> x = y.
Proof. assert (N: (0 =? 0) = true) by reflexivity.
  intros. destruct x, y; split; intros; simpl; simpl in H.
  - destruct n0. simpl in H. rewrite plus_0_r in H. apply H.
    simpl in H. remember (n0 <? n) as b; destruct b.
    symmetry in Heqb. rewrite N_ltb_true__lt in Heqb. unfold lt in Heqb.
    rewrite N_le__lt_eq in Heqb. destruct Heqb.
    rewrite N_lt__gt in H0. rewrite N_gt__pos_minus in H0.
    inversion H. rewrite H2 in H0. easy.
    rewrite H0; reflexivity.
    inversion H.
  - destruct n0. zero. apply H.
    simpl. inversion H. simpl.
    assert ((n0 <? S n0) = true). rewrite N_ltb_true__lt. omega.
    rewrite H0. assert ((n0 - n0)%nat = 0) by omega.
    rewrite H2; reflexivity.
  - inversion H. rewrite <- plus_n_Sm in H1. inversion H1.
  - inversion H.
  - destruct n0. simpl in H. assert (n = (n - 0)%nat) by omega.
    rewrite <- H0 in H. apply H. simpl in H. inversion H.
  - inversion H.
  - remember (n <? S n0) as b; destruct b. inversion H.
    rewrite <- N_le__zero_minus in H1. symmetry in Heqb.
    rewrite N_ltb_true__lt in Heqb. assert (n = n0) by omega.
    rewrite H0; reflexivity. inversion H.
  - inversion H. assert ((n0 <? S n0) = true). rewrite N_ltb_true__lt. omega.
    rewrite H0. assert ((n0 - n0)%nat = 0) by omega. rewrite H2. reflexivity.
Qed.

Lemma Z_opp_involutive: forall x: int, - - x = x.
Proof. destruct x; unfold Z_opp; simpl. destruct n. zero. zero. reflexivity. Qed.

Lemma Z_opp_lt_imp: forall x y: int, x <Z y -> -y <Z -x.
Proof. destruct x, y; unfold Z_opp, Z_le; simpl; intros.
  - destruct n0. rewrite N_nle__gt in H. inversion H. rewrite N_nle__gt in H.
    simpl. destruct n. zero. easy. simpl. omega.
  - easy.
  - destruct n0. zero. easy. zero. easy.
  - omega.
Qed.

Lemma Z_opp_distr: forall x y: int, - (x + y) = - x + - y.
Proof. destruct x, y.
  - simpl. destruct n, n0; zero. rewrite plus_n_Sm. reflexivity.
  - simpl. remember (n0 <? n) as b; remember (n =? 0) as c; destruct b, c; symmetry in Heqb, Heqc; simpl.
    + rewrite N_eqb_true__eq in Heqc. rewrite Heqc in Heqb. easy.
    + remember (n - S n0 =? 0) as d; destruct d; symmetry in Heqd.
      rewrite N_eqb_true__eq in Heqd. rewrite N_ltb_true__lt in Heqb.
      assert (n = S n0) by omega.
      assert (Init.Nat.pred n < S n0) by omega.
      rewrite <- N_ltb_true__lt in H0.
      rewrite H0. rewrite H. simpl. rewrite N_minus_itself. reflexivity.
      rewrite N_ltb_true__lt in Heqb. rewrite N_eqb_false__ne in Heqd. rewrite N_nonzero__pos in Heqd.
      assert (Init.Nat.pred n >= S n0) by omega.
      rewrite <- N_ltb_false__ge in H. rewrite H. simpl.
      assert (Init.Nat.pred (n - S n0) = (Init.Nat.pred n - S n0)%nat) by omega.
      rewrite H0. reflexivity.
    + rewrite N_eqb_true__eq in Heqc. rewrite Heqc. zero.
    + rewrite N_ltb_false__ge in Heqb. assert (Init.Nat.pred n < S n0) by omega.
      rewrite <- N_ltb_true__lt in H. rewrite H.
      assert (S (n0 - n) = (n0 - Init.Nat.pred n)%nat). destruct n0. inversion Heqb.
      rewrite H0 in Heqc. simpl in Heqc. inversion Heqc.
      destruct n. simpl in Heqc. inversion Heqc. omega.
      rewrite H0. reflexivity.
  - unfold Z_opp, Z_plus.
    remember (n <? n0) as b; remember (n0 =? 0) as c; destruct b, c; symmetry in Heqb, Heqc; simpl.
    + rewrite N_eqb_true__eq in Heqc. rewrite Heqc in Heqb. rewrite N_ltb_true__lt in Heqb. inversion Heqb.
    + rewrite N_ltb_true__lt in Heqb. remember (n0 - S n =? 0) as d; destruct d; symmetry in Heqd; simpl.
      rewrite N_eqb_false__ne in Heqc. rewrite N_eqb_true__eq in Heqd.
      assert (n0 = S n) by omega. rewrite H. simpl. assert (n < S n) by omega.
      rewrite <- N_ltb_true__lt in H0. rewrite H0. rewrite N_minus_itself. reflexivity.
      rewrite N_eqb_false__ne in Heqc, Heqd. assert (Init.Nat.pred n0 >= S n) by omega.
      rewrite <- N_ltb_false__ge in H. rewrite H.
      assert (Init.Nat.pred (n0 - S n) = (Init.Nat.pred n0 - S n)%nat) by omega.
      rewrite H0. reflexivity.
    + rewrite N_eqb_true__eq in Heqc. rewrite Heqc. zero.
    + rewrite N_ltb_false__ge in Heqb. rewrite N_eqb_false__ne in Heqc.
      assert (Init.Nat.pred n0 < S n) by omega.
      rewrite <- N_ltb_true__lt in H. rewrite H.
      assert (S (n - n0) = (n - Init.Nat.pred n0)%nat) by omega.
      rewrite H0. reflexivity.
  - simpl. rewrite plus_n_Sm. reflexivity.
Qed.

Lemma Z_opp_distr_minus: forall x y: int, - (x - y) = y - x.
Proof. unfold Z_minus. intros. rewrite (Z_opp_distr x (-y)). rewrite Z_opp_involutive. apply Z_2. Qed.

Lemma Z_opp_lt: forall x y: int, x <Z y <-> -y <Z -x.
Proof. split; intros.
  - apply Z_opp_lt_imp. apply H.
  - rewrite <- (Z_opp_involutive y), <- (Z_opp_involutive x).
    apply Z_opp_lt_imp. apply H.
Qed.

Lemma Z_pos_diff__gt: forall x y: int, x - y >Z Z_pos 0 <-> x >Z y.
Proof. intros. rewrite <- Z_opp_distr_minus. rewrite Z_opp_lt. rewrite Z_opp_involutive.
  assert (-Z Z_pos 0 = Z_pos 0) by reflexivity. rewrite H. rewrite Z_neg_diff__lt.
  reflexivity.
Qed.

Lemma Z_10_0: forall x: int,
    (  x <Z Z_pos 0 /\ ~ x = Z_pos 0 /\ ~ x >Z Z_pos 0) \/
    (~ x <Z Z_pos 0 /\   x = Z_pos 0 /\ ~ x >Z Z_pos 0) \/
    (~ x <Z Z_pos 0 /\ ~ x = Z_pos 0 /\   x >Z Z_pos 0).
Proof.
  destruct x.
  - destruct n. right. left. split. simpl. omega. split. simpl. reflexivity. simpl. omega.
    right. right. split. simpl. omega. split. unfold not. intros. inversion H. simpl. omega.
  - left. split. simpl. omega. split. unfold not. intros. inversion H. simpl. easy.
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

Lemma Z_plus_0_l: forall x: int, Z_pos 0 + x = x.
Proof. destruct x.
  - simpl. reflexivity.
  - simpl. zero.
Qed.

(** transitivity *)
Lemma Z_11_0: forall x y: int, x <Z Z_pos 0 -> y <Z Z_pos 0 -> x + y <Z Z_pos 0.
Proof. destruct x, y; intros.
  - simpl in H. rewrite N_nle__gt in H; inversion H.
  - simpl in H. rewrite N_nle__gt in H; inversion H.
  - simpl in H0. rewrite N_nle__gt in H0; inversion H0.
  - simpl. easy.
Qed.

(** transitivity *)
Theorem Z_11: forall x y z: int, x <Z y -> y <Z z -> x <Z z.
Proof. intros x y z. rewrite <- (Z_neg_diff__lt x y). rewrite <- (Z_neg_diff__lt x z). rewrite <- (Z_neg_diff__lt y z).
  assert ((x - y) + (y - z) = x - z).
  { unfold Z_minus. rewrite Z_1. rewrite <- (Z_1 (- y)).
    assert (- y + y = Z_pos 0). destruct y.
    simpl; destruct n; zero. assert (n < S n) by omega.
    rewrite <- N_ltb_true__lt in H. rewrite H. reflexivity.
    simpl. assert (n < S n) by omega. rewrite <- N_ltb_true__lt in H. rewrite H. zero.
    rewrite H. rewrite Z_plus_0_l. reflexivity. }
  rewrite <- H. apply (Z_11_0 (x - y) (y - z)).
Qed.

(** addition preserves the order *)
Theorem Z_12: forall x y z: int, x <Z y -> x + z <Z y + z.
Proof. intros x y z. rewrite <- (Z_neg_diff__lt x y). rewrite <- (Z_neg_diff__lt (x + z) (y + z)).
  unfold Z_minus. rewrite Z_1. rewrite Z_opp_distr. rewrite (Z_2 (-y) (-z)). rewrite <- (Z_1 z).
  rewrite Z_4. rewrite (Z_2 (Z_pos 0)). rewrite Z_3. intros. apply H.
Qed.


(** mult by positive number preserves the order *)
Theorem Z_13: forall x y z: int, x <Z y /\ z >Z Z_pos 0 -> x * z <Z y * z.
Proof.

Admitted.

(** Z is not a trivial ring *)
Theorem Z_14: 0 <> 1.
Proof. unfold not. intros. inversion H. Qed.

Lemma Z_not_not_equal: forall z w: int, z = w <-> ~ z <> w.
Proof.
Admitted.

Lemma Z_mult_0: forall z: int, z * Z_pos 0 = Z_pos 0.
Proof.
  destruct z; zero.
Qed.

Lemma Z_mult_neg_1: forall z: int, - z = - (Z_pos 1) * z.
Proof.
  destruct z; simpl; zero.
Qed.

Close Scope int_scope.
