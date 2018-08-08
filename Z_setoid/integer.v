Require Import Coq.omega.Omega.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import natural.
Require Import logic.

Delimit Scope integer_scope with integer.
Open Scope integer_scope.

Inductive integer: Type :=
| preint : nat -> nat -> integer.

Notation "( x , y )" := (preint x y).

(** natural order for Z *)
Definition Z_le (x y: integer) := (** x <= y iff *)
match x with
| (a1, a2) =>
  match y with
  | (b1, b2) => (a1 + b2 <= b1 + a2)
  end
end.

Lemma Z_le_refl: Reflexive Z_le.
Proof. unfold Reflexive. intros. destruct x. unfold Z_le. omega. Defined.

Lemma Z_le_tran: Transitive Z_le.
Proof. unfold Transitive. unfold Z_le. intros. destruct x, y, z. omega. Defined.

(*
Add Parametric Relation: Z_le with signature Z_eq ==> Z_eq ==> iff as Z_le_morph.
Proof.
  destruct x, y, x0, y0.
  unfold Z_eq in H. unfold Z_eq. unfold iff. unfold Z_le.
  intros. split; omega.
Defined.
*)
Add Parametric Relation:
  integer Z_le
  reflexivity proved by Z_le_refl
  transitivity proved by Z_le_tran
  as Z_le_rel.

Notation "z '<=Z' w" := (Z_le z w) (at level 70, no associativity) : type_scope.
Notation "z '<Z' w" := (~ Z_le w z) (at level 70, no associativity) : type_scope.
Notation "z '>=Z' w" := (Z_le w z) (at level 70, no associativity) : type_scope.
Notation "z '>Z' w" := (~ Z_le z w) (at level 70, no associativity) : type_scope.

Definition Z_eq (z w: integer): Prop :=
  match z with
  | (z1, z2) =>
    match w with
    | (w1, w2) => z1 + w2 = z2 + w1
    end
  end.

Notation "z =Z= w" := (Z_eq z w) (at level 70): type_scope.
Notation "z <Z> w" := (~ z =Z= w) (at level 70): type_scope.

Theorem Z_refl: Reflexive Z_eq.
Proof.
  (* reflexivity *) unfold Reflexive.
  destruct x.
  unfold Z_eq.
  apply plus_comm.
Defined.

Theorem Z_symm: Symmetric Z_eq.
Proof.
  (* symmetricity *) unfold Symmetric.
  destruct x, y.
  unfold Z_eq.
  intros.
  symmetry.
  rewrite (plus_comm n2 n), (plus_comm n1 n0).
  apply H.
Defined.

Theorem Z_tran: Transitive Z_eq.
Proof.
  unfold Transitive.
  destruct x, y, z.
  unfold Z_eq.
  intros.
  rewrite (plus_comm n n4).
  apply (N_cons_eq_plus n1 (n4 + n) (n0 + n3)).
  repeat rewrite plus_assoc.
  rewrite (plus_comm n1 n0).
  rewrite H0. rewrite <- H.
  rewrite (plus_comm _ n), plus_assoc.
  reflexivity.
Defined.

Add Parametric Relation:
  integer Z_eq
  reflexivity proved by Z_refl
  symmetry proved by Z_symm
  transitivity proved by Z_tran
  as Z.

Instance Z_eq_le_subrel: subrelation Z_eq Z_le.
Proof. unfold subrelation. destruct x, y. unfold Z_le. intros. unfold Z_eq in H. omega. Defined.

Instance Z_eq_ge_subrel: subrelation Z_eq (fun x y => Z_le y x).
Proof. unfold subrelation. destruct x, y. unfold Z_le. intros. unfold Z_eq in H. omega. Defined.


Add Parametric Morphism: Z_le with signature Z_eq ++> Z_eq ++> iff as Z_le_compat_morph.
Proof. intros. destruct x, y, x0, y0. unfold Z_eq in H, H0. unfold Z_le.
  omega. Defined.

Definition Z_plus (z w: integer) :=
  match z with
  | (z1, z2) =>
    match w with
    | (w1, w2) => (z1 + w1, z2 + w2)
    end
  end.

Add Parametric Morphism: Z_plus with signature Z_le ++> Z_le ++> Z_le as Z_le_plus_morph.
Proof. intros. destruct x, y, x0, y0. unfold Z_le in H, H0. unfold Z_plus, Z_le.
  omega. Defined.

Add Parametric Morphism: Z_plus with signature Z_eq ==> Z_eq ==> Z_eq as Z_plus_morph.
Proof. (* well-definedness of Z_plus *)
  destruct x, y, x0, y0. unfold Z_eq. unfold Z_eq in H. simpl. intros. omega. Defined.

Notation "z '+' w" := (Z_plus z w) (at level 50, left associativity) : integer_scope.
Notation "z '+Z' w" := (Z_plus z w) (at level 50, left associativity) : type_scope.

(** negation of an integer: z |-> -z *)
Definition Z_neg (z: integer) :=
match z with
| (z1, z2) => (z2, z1)
end.

Add Parametric Morphism: Z_neg with signature Z_le --> Z_le as Z_le_neg_morph.
  intros. destruct x, y. unfold Z_le in H. unfold Z_neg, Z_le.
  omega. Defined.

Add Parametric Morphism: Z_neg with signature Z_eq ==> Z_eq as Z_neg_morph.
Proof. (* well-definedness of Z_neg *)
  destruct x, y. unfold Z_eq. simpl. intros. omega. Defined.

Notation "'-' z" := (Z_neg z) (at level 35, right associativity) : integer_scope.
Notation "'-Z' z" := (Z_neg z) (at level 35, right associativity) : type_scope.

(** subtraction *)

Definition Z_minus (z w: integer) := z + - w.

Add Parametric Morphism: Z_minus with signature Z_le ++> Z_le --> Z_le as Z_le_minus_morph.
  intros. destruct x, y, x0, y0. unfold Z_le in H, H0. unfold Z_minus, Z_neg, Z_plus, Z_le.
  omega. Defined.

Add Parametric Morphism: Z_minus with signature Z_eq ==> Z_eq ==> Z_eq as Z_minus_morph.
Proof. (* well-definedness of Z_minus *)
  destruct x, y, x0, y0. unfold Z_minus, Z_eq. unfold Z_minus, Z_eq in H. simpl. intros. omega. Defined.

Notation "z '-' w" := (Z_minus z w) (at level 50, left associativity) : integer_scope.
Notation "z '-Z' w" := (Z_minus z w) (at level 50, left associativity) : type_scope.

(** multiplication *)
Definition Z_mult (z w: integer): integer :=
match z with
| (z1, z2) => 
  match w with
  | (w1, w2) => (z1 * w1 + z2 * w2, z1 * w2 + z2 * w1)
  end
end.

Notation "z '*' w" := (Z_mult z w) (at level 40, left associativity) : integer_scope.
Notation "z '*Z' w" := (Z_mult z w) (at level 40, left associativity) : type_scope.

Add Morphism Z_mult with signature Z_eq ==> Z_eq ==> Z_eq as Z_mult_morph.
Proof. (* well-definedness of Z_mult *)
  destruct x, y, x0, y0. unfold Z_eq. unfold Z_eq in H. simpl. intros.
  apply (N_cons_eq_plus (n2 * n3)%nat (n * n3 + n0 * n4 + (n1 * n6 + n2 * n5))).
  repeat rewrite plus_assoc.

  assert (((n0 + n1) * n4)%nat = ((n + n2) * n4)%nat) by (rewrite H; reflexivity).
  assert ((n1 * (n4 + n5) + n0 * n4 + n2 * n5)%nat = (n * n4 + n1 * n5 + n2 * (n4 + n5))%nat).
  { repeat rewrite mult_plus_distr_l.
    rewrite (plus_comm (n * n4) _).
    rewrite <- (plus_assoc (n1 * n5) _ _).
    rewrite (plus_assoc (n * n4)).
    rewrite <- (mult_plus_distr_r n n2 n4).
    rewrite <- H1.
    assert ((n1 * n4 + n1 * n5 + n0 * n4 + n2 * n5)%nat = (n1 * n5 + n2 * n5 + (n0 * n4 + n1 * n4))%nat) by omega.
    rewrite H2; clear H2.
    rewrite <- (mult_plus_distr_r _ _ n4). omega.
  }
  repeat rewrite <- H0 in H2.
  repeat rewrite mult_plus_distr_l in H2.
  assert ((n1 * n6 + n0 * n4 + n2 * n5 + (n0 * n3 + n1 * n3))%nat
          = (n * n4 + n1 * n5 + n0 * n3 + n2 * n6 + n2 * n3)%nat) by omega; clear H1; clear H2.
  rewrite <- mult_plus_distr_r in H3; rewrite <- H in H3; rewrite mult_plus_distr_r in H3; rewrite plus_assoc in H3.
  repeat rewrite (plus_comm _ (n2 * n3)) in H3.
  apply (N_cons_eq_plus (n2 * n3)) in H3.
  omega.
Defined.

(** zero and one *)
Notation "'0'" := (0, 0) : integer_scope.
Notation "'Z0'" := (0, 0) : type_scope.
Notation "'1'" := (1, 0) : integer_scope.
Notation "'Z1'" := (1, 0) : type_scope.

(** plus_assoc *)
Theorem Z_1: forall x y z: integer, (x + y) + z =Z= x + (y + z).
Proof. destruct x, y, z. simpl. simpl_relation. Defined.

(** plus_comm *)
Theorem Z_2: forall x y: integer, x + y =Z= y + x.
Proof. destruct x, y. simpl. simpl_relation. Defined.

(** zero as an identity for plus *)
Theorem Z_3: forall x: integer, x + 0 =Z= x.
Proof. destruct x. simpl. simpl_relation. Defined.

(** inverse element for plus *)
Theorem Z_4: forall x: integer, x + - x =Z= 0.
Proof. destruct x. unfold Z_eq. simpl_relation. Defined.

(** mult_assoc *)
Theorem Z_5: forall x y z: integer, (x * y) * z =Z= x * (y * z).
Proof. destruct x, y, z. simpl.
  repeat rewrite mult_plus_distr_l. repeat rewrite mult_plus_distr_r. repeat rewrite plus_assoc. repeat rewrite mult_assoc. omega.
Defined.

(** mult_comm *)
Theorem Z_6: forall x y: integer, x * y =Z= y * x.
Proof. destruct x, y. simpl. repeat rewrite plus_assoc.
rewrite (mult_comm n1 n), (mult_comm n0 n2), (mult_comm n1 n0), (mult_comm n n2). omega. Defined.

(** one as an identity for mult *)
Theorem Z_7: forall x: integer, x * 1 =Z= x.
Proof. destruct x. simpl. omega. Defined.

(** zero kills all! *)
Theorem Z_7_0: forall x: integer, x * 0 =Z= 0.
Proof. destruct x. simpl. omega. Defined.

(** zero kills all! *)
Theorem Z_7_1: forall x: integer, 0 * x =Z= 0.
Proof. destruct x. simpl. omega. Defined.

(** left distribution law *)
Theorem Z_8: forall x y z: integer, x * (y + z) =Z= x * y + x * z.
Proof. destruct x, y, z. simpl.
  repeat rewrite mult_plus_distr_l. repeat rewrite mult_plus_distr_r. repeat rewrite plus_assoc. repeat rewrite mult_assoc. omega. Defined.

(** right distribution law *)
Corollary Z_8_0: forall x y z: integer, (x + y) * z =Z= x * z + y * z.
Proof. intros. repeat rewrite (Z_6 _ z). apply Z_8. Defined.
(** Z is an integral domain *)
Theorem Z_9: forall x y: integer, x * y =Z= 0 -> x =Z= 0 \/ y =Z= 0.
Proof. destruct x. remember (beq_nat n n0) as b. destruct b.
  - intros. left. symmetry in Heqb.
    rewrite beq_nat_true_iff in Heqb. rewrite Heqb. simpl. reflexivity.
  - intros. right. symmetry in Heqb.
    rewrite beq_nat_false_iff in Heqb. simpl in H.
    destruct y. simpl in H. repeat (rewrite <- plus_n_O in H).
    simpl. repeat (rewrite <- plus_n_O).

    Close Scope integer_scope.

    apply N_trichotomy_ne in Heqb.
    assert (forall q r: nat, q - r <> 0 /\ q * n1 + r * n2 = q * n2 + r * n1 -> n1 = n2).
    { intros. destruct H0.
      assert (q * n1 - r * n1 = q * n2 - r * n2). { omega. }
      rewrite <- (N_minus_plus q r) in H2.
      repeat rewrite mult_plus_distr_r in H2.
      repeat rewrite N_plus_minus in H2.
      remember (q - r) as k. destruct k. omega. rewrite (N_cons_eq_mult_pos (S k)).
      apply H2. omega. omega.
    }
    destruct Heqb.
    apply (H0 n0 n). split. rewrite N_trichotomy_ne. right. omega. omega.
    apply (H0 n n0). split. rewrite N_trichotomy_ne. right. omega. omega.
    Open Scope integer_scope.
Defined.

(** natural order for Z *)
Definition Z_leb (x y: integer): bool :=
match x with
| (a1, a2) =>
  match y with
  | (b1, b2) => (a1 + b2 <=? b1 + a2)
  end
end.

(** natural order for Z *)
Definition Z_ltb (x y: integer): bool :=
match x with
| (a1, a2) =>
  match y with
  | (b1, b2) => (a1 + b2 <? b1 + a2)
  end
end.

(** natural order for Z *)
Definition Z_eqb (x y: integer): bool :=
match x with
| (a1, a2) =>
  match y with
  | (b1, b2) => (a1 + b2 =? b1 + a2)
  end
end.


Lemma Z_leb_true__le: forall x y: integer, Z_leb x y = true <-> x <=Z y.
Proof. intros. destruct x, y. simpl. apply N_leb_true__le. Defined.
Lemma Z_ltb_true__lt: forall x y: integer, Z_ltb x y = true <-> x <Z y.
Proof. intros. destruct x, y. simpl. rewrite -> N_nle__gt. apply Nat.ltb_lt. Defined.
(* Lemma Z_eqb_true__eq: forall x y: integer, (x =Z=? y) = true <-> x =Z= y.
Proof.*)
Lemma Z_leb_false__gt: forall x y: integer, Z_leb x y = false <-> x >Z y.
Proof. intros. destruct x, y. simpl. rewrite -> N_nle__gt. rewrite <- N_lt__gt. apply N_leb_false__gt. Defined.
Lemma Z_ltb_false__ge: forall x y: integer, Z_ltb x y = false <-> x >=Z y.
Proof. intros. destruct x, y. simpl. apply N_ltb_false__ge. Defined.
(* Lemma Z_eqb_false__eq: forall x y: integer, (x =Z y) = false <-> x <Z> y.
Proof. *) 

Lemma Z_neg_diff__lt: forall x y: integer, x - y <Z 0 <-> x <Z y.
  Proof. intros. destruct x, y. split; unfold Z_le; simpl; omega. Defined.
Lemma Z_no_diff__eq: forall x y: integer, x - y =Z= 0 <-> x =Z= y.
  Proof. intros. destruct x, y. split; unfold Z_le; simpl; omega. Defined.
Lemma Z_pos_diff__gt: forall x y: integer, x - y >Z 0 <-> x >Z y.
  Proof. intros. destruct x, y. split; unfold Z_le; simpl; omega. Defined.

Lemma Z_10_0: forall x: integer,
    (  x <Z 0 /\ ~ x =Z= 0 /\ ~ x >Z 0) \/
    (~ x <Z 0 /\   x =Z= 0 /\ ~ x >Z 0) \/
    (~ x <Z 0 /\ ~ x =Z= 0 /\   x >Z 0).
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
Defined.

(** trichotomy *)
Theorem Z_10: forall x y: integer,
  (  x <Z y /\ ~ x =Z= y /\ ~ x >Z y) \/
  (~ x <Z y /\   x =Z= y /\ ~ x >Z y) \/
  (~ x <Z y /\ ~ x =Z= y /\   x >Z y).
Proof.
  intros. rewrite <- Z_neg_diff__lt. rewrite <- Z_no_diff__eq. rewrite <- (Z_pos_diff__gt x y).
  apply Z_10_0.
Defined.

(** trichotomy *)
Corollary Z_10_1: forall x y: integer, x <Z y \/ x =Z= y \/ x >Z y.
Proof.
  intros.
  pose proof (Z_10 x y).
  destruct H; destruct H.
  - left. apply H.
  - destruct H. destruct H0. right. left. apply H0.
  - destruct H. destruct H0. right. right. apply H1.
Defined.

(** trichotomy *)
Corollary Z_10_2: forall x: integer, x <Z> 0 <-> x >Z 0 \/ x <Z 0.
Proof.
  intros; split.
  pose proof (Z_10 x 0);
  destruct H; destruct H.
  - right. apply H.
  - destruct H. destruct H0. intro. contradiction.
  - destruct H. destruct H0. left. apply H1.
  - intros. destruct x. unfold Z_eq. unfold Z_le in H. omega.
Defined.

Lemma Z_le_double_neg_elim: forall x y: integer, x <=Z y <-> ~~ x <=Z y.
Proof.
  destruct x, y. unfold Z_le. omega.
Defined.

Corollary Z_10_3: forall x y: integer, x <=Z y <-> x <Z y \/ x =Z= y.
Proof.
  intros. split; pose proof (Z_10_1 x y); intros.
  destruct H. left. apply H.
  destruct H. right. apply H.
  contradiction.
  destruct H. destruct x, y. unfold Z_le. unfold Z_le in H. omega.
  destruct H. apply Z_eq_ge_subrel; symmetry; apply H.
  destruct x, y. unfold Z_le, Z_eq in H, H0; unfold Z_le. omega.
Defined.

Corollary Z_10_4: forall x y: integer, x <=Z y \/ y <=Z x.
Proof. intros. pose proof (Z_10_1 x y). rewrite (Z_10_3 x y).
  destruct H. left. left. apply H.
  destruct H. left. right. apply H.
  right. rewrite (Z_10_3 y x). left. apply H.
Defined.

(** transitivity *)
Theorem Z_11: forall x y z: integer, x <Z y /\ y <Z z -> x <Z z.
Proof. intros x y z. rewrite <- (Z_neg_diff__lt x y). rewrite <- (Z_neg_diff__lt x z). rewrite <- (Z_neg_diff__lt y z).
  assert (forall a b: integer, a <Z 0 /\ b <Z 0 -> a + b <Z 0).
  { destruct a, b. intros. simpl in H; destruct H. simpl. omega. }
  assert ((x - y) + (y - z) =Z= x - z).
  { destruct x, y, z. simpl. omega. }
  intros. rewrite <- H0. apply (H (x - y) (y - z)). apply H1. Defined.

(** addition preserves the order *)
Theorem Z_12: forall x y z: integer, x <Z y <-> x + z <Z y + z.
Proof. intros x y z. rewrite <- Z_pos_diff__gt. destruct x, y, z. simpl. omega. Defined.

Lemma Z_mult_pos_pos__pos: forall a b: integer, a >Z 0 -> b >Z 0 -> a * b >Z 0.
Proof. destruct a, b. simpl. repeat rewrite <- plus_n_O.
  repeat rewrite N_not_le__gt.
  rewrite (plus_comm (n * n1) _), (plus_comm (n * n2) _).
  repeat rewrite N_nle__gt.
  apply (N_rearrange n0 n n2 n1).
Defined.

Lemma Z_mult_neg: forall v w: integer, - v * w =Z= - (v * w).
Proof. destruct v, w. simpl. omega. Defined.

Lemma Z_mult_neg_0: forall v w: integer, v * - w =Z= - (v * w).
Proof. destruct v, w. simpl. omega. Defined.

(** mult by positive number preserves the order *)
Lemma Z_13_0: forall x y z: integer, z >Z 0 -> x <Z y -> x * z <Z y * z.
Proof.
  intros x y z. rewrite <- (Z_pos_diff__gt y x). rewrite <- (Z_pos_diff__gt (y * z) _).
  assert (y * z - x * z =Z= (y - x) * z).
  { unfold Z_minus. rewrite <- Z_mult_neg. symmetry. apply Z_8_0. }
  rewrite H.
  intros.
  apply Z_mult_pos_pos__pos; [apply H1 | apply H0].
Defined.

Lemma Z_not_not_equal: forall z w: integer, z =Z= w <-> ~ z <Z> w.
Proof.
  split.
    - intros. unfold not. intros. apply H0 in H. contradiction.
    - intros. unfold not in H. destruct z, w. unfold Z_eq in H.
      remember (beq_nat (n + n2) (n0 + n1)) as b.
      destruct b.
      + symmetry in Heqb. apply beq_nat_true_iff in Heqb. simpl. auto.
      + symmetry in Heqb. apply beq_nat_false_iff in Heqb. apply H in Heqb. inversion Heqb.
Defined.

Lemma Z_mult_neg_1: forall z: integer, - z =Z= (0, 1) * z.
Proof.
  destruct z. simpl. omega.
Defined.

Lemma Z_le_inv: forall z w: integer, z <=Z w <-> - z >=Z - w.
Proof.
  destruct z, w. simpl. omega.
Defined.

Lemma Z_lt_inv: forall z w: integer, z <Z w <-> - z >Z - w.
Proof.
  destruct z, w. simpl. omega.
Defined.

Lemma Z_cons_eq_mult: forall a b c: integer, c <Z> 0 -> a =Z= b <-> c * a =Z= c * b.
Proof.
  intros.
  assert (forall z w: integer, z <Z> w <-> z >Z w \/ z <Z w).
  { split. assert (
      (  z <Z w /\ ~ z =Z= w /\ ~ z >Z w) \/
      (~ z <Z w /\   z =Z= w /\ ~ z >Z w) \/
      (~ z <Z w /\ ~ z =Z= w /\   z >Z w)
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
  assert (forall z: integer, z <Z 0 <-> - z >Z 0).
  { destruct z. unfold Z_le, Z_neg. omega. }
  assert (forall z: integer, - - z =Z= z).
  { destruct z. unfold Z_eq, Z_neg. omega. }
  intros. destruct H. destruct H3.
  - left. repeat rewrite (Z_6 c _). apply Z_13_0; auto.
  - right. repeat rewrite (Z_6 c _). apply Z_13_0; auto.
  - remember (- c) as d.
    assert (c =Z= - d). { rewrite Heqd. symmetry. apply H2. }
    rewrite H4 in H. apply H1 in H. rewrite H2 in H.
    repeat rewrite H4.
    destruct H3. right. repeat rewrite Z_mult_neg. rewrite Z_le_inv. repeat rewrite H2.
    repeat rewrite (Z_6 d _). apply Z_13_0; auto.
    left. repeat rewrite Z_mult_neg. rewrite Z_le_inv. repeat rewrite H2.
    repeat rewrite (Z_6 d _). apply Z_13_0; auto.
Defined.

(** mult by positive number preserves the order *)
Theorem Z_13: forall x y z: integer, z >Z 0 -> x <Z y <-> x * z <Z y * z.
Proof.
  intros x y z. rewrite <- (Z_pos_diff__gt y x). rewrite <- (Z_pos_diff__gt (y * z) _).
  assert (y * z - x * z =Z= (y - x) * z).
  { unfold Z_minus. rewrite <- Z_mult_neg. symmetry. apply Z_8_0. }
  rewrite H.
  intros; split; intro.
  apply Z_mult_pos_pos__pos; [apply H1 | apply H0].
  unfold not. intro.
  assert ((y -Z x) *Z z <=Z Z0).
  rewrite Z_10_3. rewrite Z_10_3 in H2. destruct H2.
  left. rewrite <- (Z_7_0 z). rewrite (Z_6 z). apply Z_13_0. apply H0. apply H2.
  right. rewrite H2. rewrite (Z_6 _ z). apply Z_7_0. contradiction.
Defined.

Theorem Z_13_1: forall x y z: integer, z >Z 0 -> x <=Z y <-> x * z <=Z y * z.
Proof.
  intros x y z H. split; rewrite (Z_le_double_neg_elim x y); rewrite (Z_le_double_neg_elim (x * z));
  apply contrapositive; apply Z_13; apply H.
Defined.

(** Z is not a trivial ring *)
Theorem Z_14: 0 <Z> 1.
Proof. unfold not. unfold Z_eq. simpl. intros. inversion H. Defined.

Definition Z_abs (z: integer): integer :=
match z with
| (m, n) => if m <? n then - z else z
end.

Add Morphism Z_abs with signature Z_eq ==> Z_eq as Z_abs_morph.
Proof.
  intros. destruct x as [x1 x2], y as [y1 y2]. simpl.
  remember (x1 <? x2) as b1; remember (y1 <? y2) as b2; destruct b1; destruct b2;
  symmetry in Heqb1; symmetry in Heqb2; simpl; intros; unfold Z_eq in H.
  - easy.
  - rewrite N_ltb_true__lt in Heqb1; rewrite N_ltb_false__ge in Heqb2.
    omega.
  - rewrite N_ltb_true__lt in Heqb2; rewrite N_ltb_false__ge in Heqb1.
    omega.
  - easy.
Defined.

Theorem Z_cons_abs_neg: forall z: integer, Z_abs (-z) =Z= Z_abs z.
Proof. destruct z. simpl.
  pose proof (N_trichotomy n n0) as T.
  destruct T.
    assert (n0 >= n) by omega.
    rewrite <- N_ltb_true__lt in H;
    rewrite <- N_ltb_false__ge in H0.
    rewrite H, H0. reflexivity.
  destruct H.
    rewrite H. reflexivity.
    assert (n >= n0) by omega.
    unfold gt in H.
    rewrite <- N_ltb_true__lt in H;
    rewrite <- N_ltb_false__ge in H0.
    rewrite H, H0. reflexivity.
Defined.

Theorem Z_abs_nonneg: forall z: integer, z >=Z 0 <-> Z_abs z =Z= z.
Proof. destruct z; split; intro. simpl. rewrite <- Z_ltb_false__ge in H.
  simpl in H. zero_in H. rewrite H. reflexivity.
  rewrite Z_le_double_neg_elim. unfold not. intros.
  assert ((n, n0) <Z Z0). unfold not. apply H0.
  simpl in H1. rewrite N_nle__gt in H1. zero_in H1. unfold gt in H1.
  rewrite <- N_ltb_true__lt in H1. simpl in H. rewrite H1 in H.
  rewrite N_ltb_true__lt in H1. simpl in H. omega.
Defined.

Theorem Z_abs_nonpos: forall z: integer, z <=Z 0 <-> Z_abs z =Z= - z.
Proof. intro. assert (--z =Z= z). destruct z. reflexivity.
  rewrite Z_le_inv. assert (-Z Z0 =Z= Z0) by reflexivity.
  rewrite H0. rewrite <- Z_cons_abs_neg. apply Z_abs_nonneg.
Defined.

Close Scope integer_scope.
