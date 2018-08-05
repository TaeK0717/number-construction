Require Import Coq.omega.Omega.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import logic.
Require Import natural.
Require Import integer.
Require Import Z_pos.

Delimit Scope rational_scope with rational.
Open Scope rational_scope.

Inductive rational: Type :=
| prerat : integer -> Z_pos -> rational.

Notation "( x '//' y )" := (prerat x y).

Definition Q_eq (p q: rational): Prop :=
match p with
| (p1 // p2) =>
  match q with
  | (q1 // q2) => (Z_mult p1 (Z_pos__Z q2)) =Z= (Z_mult (Z_pos__Z p2) q1)
  end
end.

Notation "p =Q= q" := (Q_eq p q) (at level 70): type_scope.
Notation "p <Q> q" := (~ p =Q= q) (at level 70): type_scope.

(** zero and one *)
Notation "'0'" := (Z0 // ZP1) : rational_scope.
Notation "'Q0'" := (Z0 // ZP1) : type_scope.
Notation "'1'" := (Z1 // ZP1) : rational_scope.
Notation "'Q1'" := (Z1 // ZP1) : type_scope.

Theorem Q_refl: Reflexive Q_eq.
Proof.
  (* reflexivity *) unfold Reflexive.
  destruct x.
  unfold Q_eq.
  apply Z_6.
Defined.

Theorem Q_symm: Symmetric Q_eq.
Proof.
  (* symmetricity *) unfold Symmetric.
  destruct x, y.
  unfold Q_eq.
  intros.
  symmetry.
  rewrite (Z_6 _ i), (Z_6 i0 _).
  apply H.
Defined.

Theorem Q_tran: Transitive Q_eq.
Proof.
  unfold Transitive.
  intros x y z.
  destruct x as [ix rx], y as [iy ry], z as [iz rz].
  unfold Q_eq.
  intros.
  assert (L: forall p: Z_pos, Z_pos__Z p <Z> Z0)
    by (simpl; destruct p, x; try inversion i; simpl; easy).
  assert (Z_pos__Z ry <Z> Z0) by apply (L ry).
  apply (Z_eq_mult_cons (ix *Z Z_pos__Z rz) (Z_pos__Z rx *Z iz)) in H1.
  rewrite H1; clear H1.
  repeat rewrite <- Z_5.
  rewrite (Z_6 _ ix), (Z_6 _ (Z_pos__Z rx)).
  rewrite H.
  repeat rewrite Z_5.
  assert (Z_pos__Z rx <Z> Z0) by apply L.
  apply (Z_eq_mult_cons (iy *Z Z_pos__Z rz) (Z_pos__Z ry *Z iz)) in H1.
  rewrite <- H1. apply H0.
Defined.

Add Parametric Relation:
  rational Q_eq
  reflexivity proved by Q_refl
  symmetry proved by Q_symm
  transitivity proved by Q_tran
  as Q.

Definition Q_plus (p q: rational) :=
  match p with
  | (ip // rp) =>
    match q with
    | (iq // rq) => ((ip *Z Z_pos__Z rq +Z iq *Z Z_pos__Z rp) // Z_pos_mult rp rq)
    end
  end.

Add Morphism Q_plus with signature Q_eq ==> Q_eq ==> Q_eq as Q_plus_morph.
Proof. (* well-definedness of Q_plus *)
  destruct x as [[x1 x2] [x3 x4]], y as [[y1 y2] [y3 y4]], x0 as [[z1 z2] [z3 z4]], y0 as [[w1 w2] [w3 w4]].
  simpl. simpl in H.
  repeat rewrite mult_0_r. repeat rewrite <- plus_n_O. simpl.
  repeat rewrite mult_0_r in H. repeat rewrite <- plus_n_O in H. simpl in H.
  intros.
  repeat rewrite mult_plus_distr_r, mult_plus_distr_l.
  assert (forall a b c d: nat, a * c * (b * d) = a * b * (c * d))
    by (intros; rewrite <- mult_assoc, (mult_comm c (b * d)), <- mult_assoc, (mult_comm d c);
        repeat rewrite mult_assoc; easy).
  rewrite (H1 x1 y3), (H1 x3 y2), plus_assoc, <- (plus_assoc _ _ (x3 * y2 * (z3 * w3))),
          (plus_comm (z1 * x3 * (y3 * w3))), plus_assoc, <- mult_plus_distr_r, H, 
          mult_plus_distr_r, (H1 x2 y3), (H1 x3 y1),
          <- (plus_assoc (x2 * y3 * (z3 * w3)) (z2 * x3 * (y3 * w3))),
          (plus_comm (z2 * x3 * (y3 * w3))), <- (plus_assoc (x3 * y1 * (z3 * w3))),
          (plus_comm (x3 * z3 * (w1 * y3))), (mult_comm z2 x3), <- (mult_assoc x3 z2),
          (mult_comm y3 w3), (mult_comm x3 (z2 * (w3 * y3))),
          <- (mult_assoc x3 z3 (w1 * y3)), (mult_comm x3 (z3 * (w1 * y3))),
          <- (mult_assoc z2 (w3 * y3) x3), <- (mult_assoc z3 (w1 * y3) x3),
          <- (mult_assoc w3 y3 x3), <- (mult_assoc w1 y3 x3),
          (mult_assoc z2 w3 _), (mult_assoc z3 w1 _), <- (mult_plus_distr_r (z2 * w3)),
          <- H0, mult_plus_distr_r.
  repeat rewrite mult_assoc; repeat rewrite plus_assoc.
  rewrite <- (mult_assoc z1 x3), <- (mult_assoc z1 (x3 * w3)), <- (mult_assoc x3 w3),
          (mult_comm x3 (w3 * y3)), <- (mult_assoc x3 z3), <- (mult_assoc x3 (z3 * w2)),
          (mult_comm x3 (z3 * w2 * y3)).
  repeat rewrite mult_assoc. reflexivity.
Defined.

Notation "p '+' q" := (Q_plus p q) (at level 50, left associativity) : rational_scope.
Notation "p '+Q' q" := (Q_plus p q) (at level 50, left associativity) : type_scope.

(** negation of a rational number: q |-> -q *)
Definition Q_neg (q: rational) :=
  match q with
  | (iq // rq) => (-Z iq // rq)
  end.

Add Morphism Q_neg with signature Q_eq ==> Q_eq as Q_neg_morph.
Proof. (* well-definedness of Q_neg *)
  destruct x as [[x1 x2] [x3 x4]], y as [[y1 y2] [y3 y4]].
  simpl. repeat rewrite mult_0_r. repeat rewrite <- plus_n_O. simpl. intros. omega.
Defined.

Notation "'-' q" := (Q_neg q) (at level 35, right associativity) : rational_scope.
Notation "'-Q' q" := (Q_neg q) (at level 35, right associativity) : type_scope.

(** subtraction *)

Definition Q_minus (p q: rational) := p + -q.

Add Morphism Q_minus with signature Q_eq ==> Q_eq ==> Q_eq as Q_minus_morph.
Proof. (* well-definedness of Z_minus *)
  unfold Q_minus. intros. now rewrite H, H0.
Defined.

Notation "p '-' q" := (Q_minus p q) (at level 50, left associativity) : rational_scope.
Notation "p '-Q' q" := (Q_minus p q) (at level 50, left associativity) : type_scope.

(** multiplication *)
Definition Q_mult (p q: rational) := 
  match p with
  | (ip // rp) =>
    match q with
    | (iq // rq) => (ip *Z iq // Z_pos_mult rp rq)
    end
  end.

Add Morphism Q_mult with signature Q_eq ==> Q_eq ==> Q_eq as Q_mult_morph.
Proof. (* well-definedness of Z_minus *)
  destruct x as [[x1 x2] [x3 x4]], y as [[y1 y2] [y3 y4]], x0 as [[z1 z2] [z3 z4]], y0 as [[w1 w2] [w3 w4]].
  simpl. simpl in H.
  repeat rewrite mult_0_r. repeat rewrite <- plus_n_O. simpl.
  repeat rewrite mult_0_r in H. repeat rewrite <- plus_n_O in H. simpl in H.
  intros.
  repeat rewrite mult_plus_distr_l. repeat rewrite mult_plus_distr_r.
  assert (forall a b c d: nat, (a * b) * (c * d) = (a * c) * (b * d)).
  intros. rewrite mult_assoc. rewrite <- (mult_assoc a b c). rewrite (mult_comm b c).
  repeat rewrite mult_assoc. reflexivity.
  repeat rewrite (H1 x3 z3); repeat rewrite (H1 _ _ y3 w3).
  rewrite (N_cons_eq_plus (x3 * y2 * (z1 * w3) + x3 * y1 * (z2 * w3)) (x1 * y3 * (z1 * w3) + x2 * y3 * (z2 * w3) +
 (x3 * y1 * (z3 * w2) + x3 * y2 * (z3 * w1))) (x1 * y3 * (z2 * w3) + x2 * y3 * (z1 * w3) +
 (x3 * y1 * (z3 * w1) + x3 * y2 * (z3 * w2)))).
  repeat rewrite plus_assoc. rewrite (plus_comm (x3 * y2 * (z1 * w3)) (x3 * y1 * (z2 * w3))).
  rewrite <- (plus_assoc (x3 * y1 * (z2 * w3))). rewrite <- mult_plus_distr_r.
  rewrite (plus_comm (x3 * y2) (x1 * y3)). rewrite H. rewrite mult_plus_distr_r.
  assert ((x3 * y1 * (z2 * w3) + x3 * y2 * (z1 * w3) + x1 * y3 * (z2 * w3) +
           x2 * y3 * (z1 * w3) + x3 * y1 * (z3 * w1) + x3 * y2 * (z3 * w2))%nat
        = (x3 * y2 * (z1 * w3) + x1 * y3 * (z2 * w3) + x2 * y3 * (z1 * w3) +
           x3 * y2 * (z3 * w2) + (x3 * y1 * (z2 * w3) + x3 * y1 * (z3 * w1)))%nat) by omega.
  rewrite H2; clear H2.
  rewrite <- mult_plus_distr_l. rewrite <- H0. rewrite mult_plus_distr_l.
  assert (
    (x3 * y1 * (z2 * w3) + (x2 * y3 * (z1 * w3) + x3 * y1 * (z1 * w3)) +
     x2 * y3 * (z2 * w3) + x3 * y1 * (z3 * w2) + x3 * y2 * (z3 * w1))%nat = 
    ((x2 * y3 * (z1 * w3) + x3 * y1 * (z3 * w2)) + (x3 * y1 * (z2 * w3) +
      x2 * y3 * (z2 * w3) + x3 * y1 * (z1 * w3) + x3 * y2 * (z3 * w1)))%nat
  ) by omega.
  rewrite H2; clear H2.
  assert (
    (x3 * y2 * (z1 * w3) + x1 * y3 * (z2 * w3) + x2 * y3 * (z1 * w3) +
     x3 * y2 * (z3 * w2) + (x3 * y1 * (z1 * w3) + x3 * y1 * (z3 * w2)))%nat = 
    ((x2 * y3 * (z1 * w3) + x3 * y1 * (z3 * w2)) + ((x3 * y2 * (z1 * w3) + 
     x1 * y3 * (z2 * w3) + x3 * y1 * (z1 * w3) + x3 * y2 * (z3 * w2))))%nat
  ) by omega.
  rewrite H2; clear H2.
  rewrite <- (N_cons_eq_plus (x2 * y3 * (z1 * w3) + x3 * y1 * (z3 * w2))).
  rewrite <- mult_plus_distr_r. rewrite (plus_comm (x3 * y1)). rewrite <- H. rewrite mult_plus_distr_r.
  assert (
    (x3 * y2 * (z1 * w3) + x1 * y3 * (z2 * w3) + x3 * y1 * (z1 * w3) + x3 * y2 * (z3 * w2))%nat
  = (x3 * y2 * (z1 * w3) + x3 * y2 * (z3 * w2) + (x3 * y1 * (z1 * w3) + x1 * y3 * (z2 * w3)))%nat
  ) by omega.
  rewrite H2; clear H2.
  rewrite <- mult_plus_distr_l. rewrite H0. rewrite mult_plus_distr_l. omega.
Defined.

Notation "p '*' q" := (Q_mult p q) (at level 40, left associativity) : rational_scope.
Notation "p '*Q' q" := (Q_mult p q) (at level 40, left associativity) : type_scope.

Definition Q_nonzero: Set := {q : rational | q <Q> 0}.

Definition Q_numerator (q: rational) :=
  match q with
  | (iq // rq) => iq
  end.

Definition Q_denominator (q: rational) :=
  match q with
  | (iq // rq) => rq
  end.

Lemma Q_zero_iff: forall q: rational, q =Q= 0 <-> Q_numerator q =Z= Z0.
Proof.
  intros [[q1 q2] [q3 q4]]; split; intros;
  simpl; simpl in H;
  repeat rewrite mult_0_r; repeat rewrite mult_0_r in H;
  repeat rewrite <- plus_n_O; repeat rewrite <- plus_n_O in H;
  simpl; simpl in H.
  - assert (forall n: nat, (n * 1)%nat = n) by (intros; omega).
    repeat rewrite H0 in H. apply H.
  - rewrite H; reflexivity.
Defined.

Lemma Q_nonzero__iff: forall q: rational, q <Q> 0 <-> Q_numerator q <Z> Z0.
Proof.
  intros. rewrite Q_zero_iff. reflexivity.
Defined.

Definition N_sgn_diff__Z (n m: nat): integer :=
  if n <? m then -Z Z1 else if n =? m then Z0 else Z1.

Lemma Z_sgn_diff__nonzero: forall n m: nat, n <> m <-> N_sgn_diff__Z n m <Z> Z0.
Proof. 
  intros. split. unfold N_sgn_diff__Z. remember (n <? m) as b.
  destruct b. easy.
  remember (n =? m) as c. destruct c.
  symmetry in Heqc. rewrite Nat.eqb_eq in Heqc. contradiction.
  easy.
  unfold N_sgn_diff__Z. remember (n <? m) as b.
  destruct b. intros. symmetry in Heqb. rewrite Nat.ltb_lt in Heqb. omega.
  remember (n =? m) as c. destruct c.
  intros. simpl in H. omega.
  pose proof (Nat.eq_dec n m) as T. destruct T.
  rewrite <- Nat.eqb_eq in e. rewrite e in Heqc. inversion Heqc.
  intros. apply n0.
Defined.

Lemma N_abs_diff: forall q1 q2: nat, q1 <> q2 -> (0 <? q1 - q2 + (q2 - q1)) = true.
Proof.
  intros. rewrite N_trichotomy_ne in H. rewrite N_ltb_true__lt. destruct H; omega.
Defined.

(** reciprocal of a rational number: q |-> -q *)
Definition Q_recip (q: Q_nonzero): Q_nonzero.
  destruct q as [[[q1 q2] [q3 q4]] Hq].
  remember (fun x => (0 <? x) = true) as f.
  simpl in Hq; repeat rewrite mult_1_r in Hq; zero_in Hq; simpl in Hq.
  remember (exist (fun x => (0 <? x) = true) ((q1 - q2) + (q2 - q1))%nat ((N_abs_diff q1 q2) Hq)) as m.
  exists ( ((N_sgn_diff__Z q1 q2) *Z (q3, 0)) // m ).

  assert ((q1, q2) <Z> Z0). { simpl. repeat rewrite plus_0_r. apply Hq. }
  rewrite Q_nonzero__iff.
  simpl.
  pose proof Hq as H0.
  rewrite N_trichotomy_ne in H0.

  assert (forall z w: integer, z <Z> Z0 /\ w <Z> Z0 -> z *Z w <Z> Z0). {
    intros [z1 z2] [w1 w2]. simpl. repeat rewrite plus_0_r. intros. destruct H1.
    rewrite N_trichotomy_ne in H1; rewrite N_trichotomy_ne in H2; rewrite N_trichotomy_ne.
    destruct H1, H2.
    - right. apply N_rearrange.
      apply H1. apply H2.
    - left. apply N_rearrange.
      apply H1. apply H2.
    - left. rewrite (plus_comm (z1 * w1)), (plus_comm (z1 * w2)). apply N_rearrange.
      apply H1. apply H2.
    - right. rewrite (plus_comm (z1 * w2)), (plus_comm (z1 * w1)). apply N_rearrange.
      apply H1. apply H2.
  }
  apply H1. split.
  assert (forall a b: nat, a > b -> (a <? b) = false /\ (a =? b) = false).
  { induction a. intros. inversion H2. intros. destruct b. split; unfold Nat.ltb; reflexivity.
  assert (S a > S b -> a > b) by omega. apply H3 in H2.
  apply IHa in H2. destruct H2.
  split. unfold Nat.ltb. unfold Nat.ltb in H2.
  rewrite N_leb_false__gt. rewrite N_leb_false__gt in H2. omega.
  rewrite N_eqb_false__ne. rewrite N_eqb_false__ne in H4. omega.
  }

  unfold N_sgn_diff__Z.

  unfold is_true in q4.
  rewrite Nat.ltb_lt in q4.
  simpl in H0. repeat rewrite <- plus_n_O in H0. destruct H0.

  apply Z_sgn_diff__nonzero. apply Hq.
  apply Z_sgn_diff__nonzero. apply Hq.
  simpl. unfold is_true in q4. rewrite Nat.ltb_lt in q4. omega.
Defined.

Definition Q_nonzero_eq (p q: Q_nonzero): Prop := (proj1_sig p) =Q= (proj1_sig q).

Add Morphism Q_recip with signature Q_nonzero_eq ==> Q_nonzero_eq as Q_recip_morph.
Proof. (* well-definedness of Q_recip *)
  destruct x as [[[x1 x2] [x3 x4]] x5], y as [[[y1 y2] [y3 y4]] y5].
  unfold Q_nonzero_eq. intros. simpl in H. unfold Q_recip.
  simpl. zero_in H. simpl in H. unfold Z_pos__Z. simpl.
  unfold N_sgn_diff__Z.
  zero_in x5; zero_in y5.
  assert (mult_1_r: forall n:nat, (n * 1)%nat = n) by (intros; omega).
  repeat rewrite mult_1_r in x5; repeat rewrite mult_0_r, plus_0_r in x5; simpl in x5.
  repeat rewrite mult_1_r in y5; repeat rewrite mult_0_r, plus_0_r in y5; simpl in y5.
  rewrite N_trichotomy_ne in x5, y5.
  destruct x5, y5.
  - assert (NDx: (x1 - x2)%nat = 0%nat) by omega.
    assert (NDy: (y1 - y2)%nat = 0%nat) by omega.
    rewrite <- N_ltb_true__lt in H0, H1.
    rewrite H0, H1, NDx, NDy; zero; simpl.
    rewrite (N_cons_eq_plus (x3 * y1 + x1 * y3)).
    rewrite <- plus_assoc, (plus_comm (x1 * y3)), <- mult_plus_distr_r, N_minus_plus.
    rewrite <- plus_assoc, (plus_comm _ (x3 * (y2 - y1))), plus_assoc, <- mult_plus_distr_l, (plus_comm y1 (y2 - y1)%nat), N_minus_plus.
    omega. rewrite N_ltb_true__lt in H0. omega. rewrite N_ltb_true__lt in H1. omega.
  - assert (NDx: (x1 - x2)%nat = 0%nat) by omega.
    assert (NDy: (y2 - y1)%nat = 0%nat) by omega.
    rewrite <- N_ltb_true__lt in H0.
    assert (y1 >= y2) by omega.
    assert (y1 <> y2) by omega.
    rewrite <- N_ltb_false__ge in H2.
    rewrite <- N_eqb_false__ne in H3.
    rewrite H0, H2, H3, NDx, NDy; zero; simpl.
    rewrite (N_cons_eq_plus (x3 * y2 + x1 * y3)). zero.
    rewrite (plus_comm (x3 * (y1 - y2))%nat), <- plus_assoc, (plus_assoc (x1 * y3)%nat), (plus_comm (x1 * y3)%nat),
    <- mult_plus_distr_r, N_minus_plus.
    rewrite (plus_comm (x2 * y3)%nat), plus_assoc, <- mult_plus_distr_l, (plus_comm y2), N_minus_plus.
    omega. rewrite N_ltb_true__lt in H0. omega. rewrite N_ltb_true__lt in H0. omega.
  - assert (NDx: (x2 - x1)%nat = 0%nat) by omega.
    assert (NDy: (y1 - y2)%nat = 0%nat) by omega. 
    rewrite <- N_ltb_true__lt in H1.
    assert (x1 >= x2) by omega.
    assert (x1 <> x2) by omega.
    rewrite <- N_ltb_false__ge in H2.
    rewrite <- N_eqb_false__ne in H3.
    rewrite H1, H2, H3, NDx, NDy; zero; simpl.
    rewrite (N_cons_eq_plus (x3 * y1 + x2 * y3)). zero.
    assert ((x3 * y1 + x2 * y3 + (x3 * (y2 - y1) + (x1 - x2) * y3))%nat = (x3 * (y2 - y1) + x3 * y1 + ((x1 - x2) * y3 + x2 * y3))%nat) by omega.
    rewrite H4. rewrite <- mult_plus_distr_l, <- mult_plus_distr_r. repeat rewrite N_minus_plus.
    omega. omega. rewrite N_ltb_true__lt in H1. omega.
  - assert (NDx: (x2 - x1)%nat = 0%nat) by omega.
    assert (NDy: (y2 - y1)%nat = 0%nat) by omega.
    assert (x1 >= x2) by omega.
    assert (x1 <> x2) by omega.
    assert (y1 >= y2) by omega.
    assert (y1 <> y2) by omega.
    rewrite <- N_ltb_false__ge in H2.
    rewrite <- N_eqb_false__ne in H3.
    rewrite <- N_ltb_false__ge in H4.
    rewrite <- N_eqb_false__ne in H5.
    rewrite H2, H3, H4, H5, NDx, NDy; zero; simpl.
    rewrite (N_cons_eq_plus (x2 * y3 + x3 * y2)).
    rewrite <- plus_assoc, <- mult_plus_distr_l, (plus_comm y2), N_minus_plus.
    rewrite <- plus_assoc, (plus_comm (x3 * y2)), plus_assoc, (plus_comm (x2 * y3) ((x1 - x2) * y3)), <- mult_plus_distr_r, N_minus_plus.
    omega. omega. omega.
Defined.

Theorem Q_nonzero_refl: Reflexive Q_nonzero_eq.
Proof.
  (* reflexivity *) unfold Reflexive.
  destruct x. unfold Q_nonzero_eq. reflexivity.
Defined.

Theorem Q_nonzero_symm: Symmetric Q_nonzero_eq.
Proof.
  (* symmetricity *) unfold Symmetric.
  destruct x, y. unfold Q_nonzero_eq. symmetry. apply H.
Defined.

Theorem Q_nonzero_tran: Transitive Q_nonzero_eq.
Proof.
  unfold Transitive.
  destruct x, y, z. unfold Q_nonzero_eq. intros. rewrite <- H in H0. apply H0.
Defined.

Add Parametric Relation:
  Q_nonzero Q_nonzero_eq
  reflexivity proved by Q_nonzero_refl
  symmetry proved by Q_nonzero_symm
  transitivity proved by Q_nonzero_tran
  as Q_nz.

Definition Q_nonzero_mult (p q: Q_nonzero): Q_nonzero.
  exists ((proj1_sig p) * (proj1_sig q)).
  destruct p, q. simpl.
  destruct x, x0.
  rewrite Q_nonzero__iff. simpl.
  rewrite Q_nonzero__iff in n, n0. simpl in n, n0.
  unfold not. intro.
  apply Z_9 in H. destruct H;
  contradiction.
Defined.

Lemma Q_nonzero__Q_injective:
  forall p q: Q_nonzero, proj1_sig p =Q= proj1_sig q -> Q_nonzero_eq p q.
Proof.
  intros [x1 i1] [x2 i2]; simpl; intros e. unfold Q_nonzero_eq. simpl. apply e.
Defined.

Definition Q_nonzero_1: Q_nonzero.
  exists 1.
  simpl. easy.
Defined.

Notation "'/' q" := (Q_recip q) (at level 35, right associativity) : rational_scope.
Notation "'/Q' q" := (Q_recip q) (at level 35, right associativity) : type_scope.

Theorem Q_1: forall p q r: rational, p + q + r =Q= p + (q + r).
Proof. intros. destruct p, q, r. unfold Q_plus.
  assert (Z_pos_mult (Z_pos_mult z z0) z1 = Z_pos_mult z (Z_pos_mult z0 z1)).
  destruct z, z0, z1. apply Z_pos__N_injective. simpl. symmetry. apply mult_assoc.
  assert ((i *Z Z_pos__Z z0 +Z i0 *Z Z_pos__Z z) *Z Z_pos__Z z1 +Z i1 *Z Z_pos__Z (Z_pos_mult z z0)
          =Z= i *Z Z_pos__Z (Z_pos_mult z0 z1) +Z (i0 *Z Z_pos__Z z1 +Z i1 *Z Z_pos__Z z0) *Z Z_pos__Z z).
  repeat rewrite Z_8_0.
    assert (forall a b: Z_pos, Z_pos__Z (Z_pos_mult a b) =Z= Z_pos__Z a *Z Z_pos__Z b).
    intros. unfold Z_pos__Z. rewrite Z_pos_mult_compat. unfold Z_mult. zero.
  repeat rewrite H0. rewrite (Z_6 (Z_pos__Z z)). rewrite (Z_5 i0 (Z_pos__Z z)). rewrite (Z_6 (Z_pos__Z z)).
  repeat rewrite <- Z_5. rewrite <- Z_1. reflexivity.
  unfold Q_eq. rewrite H, H0. rewrite (Z_6 (Z_pos__Z (Z_pos_mult z (Z_pos_mult z0 z1)))). reflexivity.
Defined.

Theorem Q_2: forall p q: rational, p + q =Q= q + p.
Proof. intros. destruct p, q. unfold Q_plus. unfold Q_eq.
  unfold Z_pos__Z. rewrite Z_pos_mult_compat. rewrite Z_8, Z_8_0. unfold Z_pos__Z. rewrite Z_pos_mult_compat.
  rewrite (Z_6 (i *Z (proj1_sig z0, 0))), (Z_6 (i0 *Z (proj1_sig z, 0))).
  rewrite (mult_comm (Z_pos__N z0)).
  apply Z_2.
Defined.

Theorem Q_3: forall q: rational, q + 0 =Q= q.
Proof. intros. destruct q. unfold Q_plus. unfold Q_eq. rewrite Z_3. rewrite (Z_6 _ i).
  unfold Z_pos__Z. rewrite Z_5. rewrite Z_pos_mult_compat. simpl. zero.
  assert (forall a: nat, (a * 1)%nat = a) by (intros; omega). rewrite H. reflexivity.
Defined.

Theorem Q_4: forall q: rational, q + -q =Q= 0.
Proof. intros. destruct q. unfold Q_neg, Q_plus, Q_eq.
  assert (forall a b: integer, -Z a *Z b =Z= -Z (a *Z b)).
  { destruct a, b. simpl. omega. }
  rewrite H. rewrite Z_4. simpl. zero.
Defined.

Theorem Q_5: forall p q r: rational, p * q * r =Q= p * (q * r).
Proof. intros. destruct p, q, r. unfold Q_mult, Q_eq, Z_pos__Z.
  repeat rewrite Z_pos_mult_compat. rewrite (Z_5 i i0 i1). rewrite Z_6. rewrite <- mult_assoc. reflexivity.
Defined.

Theorem Q_6: forall p q: rational, p * q =Q= q * p.
Proof. intros. destruct p, q. unfold Q_mult, Q_eq, Z_pos__Z. repeat rewrite Z_pos_mult_compat.
  rewrite Z_6. rewrite (Z_6 i i0). rewrite mult_comm. reflexivity.
Defined.

Theorem Q_7: forall q: rational, q * 1 =Q= q.
Proof. intros. destruct q. unfold Q_mult, Q_eq, Z_pos__Z. rewrite Z_pos_mult_compat. rewrite Z_7, Z_6.
  assert ((Z_pos__N z * Z_pos__N ZP1)%nat = Z_pos__N z) by (simpl; omega).
  rewrite H. reflexivity.
Defined.

Ltac one:= repeat rewrite mult_1_r.

Theorem Q_8: forall q: Q_nonzero, Q_nonzero_eq (Q_nonzero_mult q (/q)) (Q_nonzero_1).
Proof. intros. apply Q_nonzero__Q_injective. simpl. destruct q as [[[q1 q2] [q3 q4]] q5].
  unfold Q_recip. simpl. zero. unfold N_sgn_diff__Z. simpl in q5. zero_in q5. simpl in q5.
  pose proof (N_trichotomy q1 q2) as H. destruct H.
  - assert ((q1 - q2)%nat = 0%nat) by omega.
    rewrite <- N_ltb_true__lt in H. rewrite H. simpl. zero. simpl. rewrite H0. simpl.
    rewrite <- mult_plus_distr_r. rewrite (mult_comm q2 q3), (mult_comm q1 q3). one.
    rewrite <- mult_plus_distr_l. rewrite (plus_comm q1). rewrite N_minus_plus.
    reflexivity. rewrite N_ltb_true__lt in H. omega.
  - destruct H. assert (q1 >= q2) by omega. rewrite <- N_eqb_true__eq in H.
    rewrite <- N_ltb_false__ge in H0. rewrite H0, H. simpl. zero. one. simpl.
    rewrite N_eqb_true__eq in H. rewrite H. omega.
    assert (q1 >= q2) by omega. assert (q1 <> q2) by omega.
    rewrite <- N_ltb_false__ge in H0. rewrite <- N_eqb_false__ne in H1.
    rewrite H0, H1. simpl. zero. one. simpl.
    assert ((q2 - q1)%nat = 0%nat) by omega.
    rewrite H2. rewrite (mult_comm q2 q3). zero. rewrite <- mult_plus_distr_l.
    rewrite (plus_comm q2). rewrite N_minus_plus. apply mult_comm. omega.
Defined.

Theorem Q_9: forall p q r: rational, p * (q + r) =Q= p * q + p * r.
Proof. intros. destruct p, q, r.
  unfold Q_mult, Q_eq, Q_plus, Z_pos__Z. repeat rewrite Z_pos_mult_compat.
  repeat rewrite Z_8. repeat rewrite Z_8_0.
  rewrite (Z_6 (i *Z i0)). rewrite <- (Z_5 _ _ (i *Z i0)).
  assert (forall a b: nat, (a, 0) *Z (b, 0) =Z= ((a * b)%nat, 0)).
  intros. unfold Z_mult. zero.
  rewrite (Z_6 _ (i *Z i1 *Z (Z_pos__N z * Z_pos__N z0, 0))).
  rewrite (Z_5 (i *Z i1)).
  rewrite <- (Z_5 i i0), (Z_5 (i *Z i0)).
  rewrite <- (Z_5 i i1), (Z_5 (i *Z i1)).
  repeat rewrite H.
  rewrite (Z_6 _ (i *Z i0)).
  repeat rewrite mult_assoc.
  unfold Z_pos__N.
  rewrite (mult_comm (proj1_sig z * proj1_sig z0) (proj1_sig z1)), mult_assoc.
  rewrite (mult_comm (proj1_sig z * proj1_sig z0 * proj1_sig z) (proj1_sig z0)).
  repeat rewrite mult_assoc.
  reflexivity.
Defined.

(** natural order for Q *)
Definition Q_le (p q: rational) := (** p <= q iff *)
match p with
| (ip // rp) =>
  match q with
  | (iq // rq) => (ip *Z Z_pos__Z rq <=Z iq *Z Z_pos__Z rp)
  end
end.

Add Parametric Morphism: Q_le with signature Q_eq ==> Q_eq ==> iff as Q_le_morph.
Proof.
  intros [[ix lx] rx] [[iy ly] ry] Hxy [[iz lz] rz] [[iw lw] rw] Hzw.
  unfold Q_le, Z_pos__Z, Z_mult. zero. simpl.
  unfold Q_eq, Z_pos__Z, Z_mult in Hxy, Hzw. zero_in Hxy; zero_in Hzw. simpl in Hxy, Hzw.
  rewrite (N_cons_le_mult_pos (proj1_sig ry) (ix * proj1_sig rz + lz * proj1_sig rx)).
  repeat rewrite mult_plus_distr_l; repeat rewrite mult_assoc. rewrite (mult_comm _ ix).
  rewrite (N_cons_le_plus (proj1_sig rx * ly * proj1_sig rz) (ix * proj1_sig ry * proj1_sig rz + proj1_sig ry * lz * proj1_sig rx)).
  rewrite plus_assoc. rewrite (plus_comm (proj1_sig rx * ly * proj1_sig rz)).
  rewrite <- mult_plus_distr_r. rewrite Hxy. rewrite mult_plus_distr_r.
  rewrite plus_assoc. rewrite (plus_comm _ (proj1_sig ry * lx * proj1_sig rz)).
  rewrite (mult_comm _ lx).
  rewrite <- (plus_assoc (lx * proj1_sig ry * proj1_sig rz)).
  rewrite <- (N_cons_le_plus (lx * proj1_sig ry * proj1_sig rz)).

  rewrite (N_cons_le_mult_pos (proj1_sig rz) (iy * proj1_sig rw + lw * proj1_sig ry)).
  repeat rewrite mult_plus_distr_l; repeat rewrite mult_assoc.
  rewrite (N_cons_le_plus (iz * proj1_sig rw * proj1_sig ry) (proj1_sig rz * iy * proj1_sig rw + proj1_sig rz * lw * proj1_sig ry)).
  rewrite (plus_comm (iz * proj1_sig rw * proj1_sig ry)), <- plus_assoc. rewrite <- mult_plus_distr_r.
  rewrite (plus_comm (proj1_sig rz * lw)). rewrite Hzw. rewrite mult_plus_distr_r.
  rewrite (plus_comm (lz * proj1_sig rw * proj1_sig ry)).
  repeat rewrite plus_assoc.
  repeat rewrite (plus_comm _ (proj1_sig rz * iw * proj1_sig ry)).
  repeat rewrite <- plus_assoc.
  rewrite <- (N_cons_le_plus (proj1_sig rz * iw * proj1_sig ry)).

  repeat rewrite (mult_comm _ (proj1_sig rx)), <- (mult_assoc (proj1_sig rx)).
  repeat rewrite <- (mult_plus_distr_l (proj1_sig rx)).
  rewrite <- (N_cons_le_mult_pos (proj1_sig rx)).

  repeat rewrite (mult_comm _ (proj1_sig rw)).
  repeat rewrite <- (mult_assoc (proj1_sig rw)).
  repeat rewrite <- mult_plus_distr_l.
  rewrite <- (N_cons_le_mult_pos (proj1_sig rw)).
  repeat rewrite (mult_comm (proj1_sig ry)), (mult_comm (proj1_sig rz)).
  rewrite (plus_comm (iz * proj1_sig ry)). reflexivity.

  destruct rw. simpl. unfold gt. rewrite <- N_ltb_true__lt. apply i.
  destruct rx. simpl. unfold gt. rewrite <- N_ltb_true__lt. apply i.
  destruct rz. simpl. unfold gt. rewrite <- N_ltb_true__lt. apply i.
  destruct ry. simpl. unfold gt. rewrite <- N_ltb_true__lt. apply i.
Defined.

Notation "z '<=Q' w" := (Q_le z w) (at level 70, no associativity) : type_scope.
Notation "z '<Q' w" := (~ Q_le w z) (at level 70, no associativity) : type_scope.
Notation "z '>=Q' w" := (Q_le w z) (at level 70, no associativity) : type_scope.
Notation "z '>Q' w" := (~ Q_le z w) (at level 70, no associativity) : type_scope.

Theorem Q_le_refl: subrelation Q_le Q_le.
Proof. unfold subrelation. destruct x, y. unfold Q_le. intros. apply H. Defined.

Lemma Q_le_iff_neg: forall x: rational, x <=Q 0 <-> Q_numerator x <=Z Z0.
Proof. destruct x.
  unfold Q_le. simpl. rewrite Z_7. reflexivity.
Defined.

Lemma Q_le_iff_pos: forall x: rational, x >=Q 0 <-> Q_numerator x >=Z Z0.
Proof. destruct x.
  unfold Q_le. unfold Z_pos__Z.
  assert (proj1_sig ZP1 = 1%nat) by reflexivity. rewrite H.
  assert (Z0 *Z (proj1_sig z, 0) =Z= Z0) by reflexivity. rewrite H0.
  assert (Q_numerator (i // z) =Z= i) by reflexivity. rewrite H1.
  rewrite Z_7. reflexivity.
Defined.

Lemma Q_eq_iff: forall x: rational, x =Q= 0 <-> Q_numerator x =Z= Z0.
Proof. destruct x.
  unfold Q_eq. unfold Z_pos__Z.
  assert (proj1_sig ZP1 = 1%nat) by reflexivity. rewrite H.
  assert ((proj1_sig z, 0) *Z Z0 =Z= Z0) by reflexivity. rewrite H0.
  assert (Q_numerator (i // z) =Z= i) by reflexivity. rewrite H1.
  rewrite Z_7. reflexivity.
Defined.

Lemma Q_neg_diff__lt: forall x y: rational, x - y <Q 0 <-> x <Q y.
Proof. intros. destruct x, y.
  assert (forall t: integer, Z0 *Z t =Z= Z0). destruct t. zero.
  assert (forall a b: integer, a +Z -Z b =Z= a -Z b).
         destruct a, b. unfold Z_neg, Z_plus, Z_minus. reflexivity.
  assert (forall a b: integer, -Z a *Z b =Z= -Z (a *Z b)).
         destruct a, b. unfold Z_neg, Z_mult, Z_eq. omega.
  unfold Q_le, Z_pos__Z, Q_minus, Q_neg, Q_plus.
  repeat rewrite H. rewrite Z_8_0.
  repeat rewrite H1. rewrite H0. unfold Z_minus. rewrite Z_neg_diff__lt.
  repeat rewrite Z_5. simpl. zero. one. easy.
Defined.
Lemma Q_no_diff__eq: forall x y: rational, x - y =Q= 0 <-> x =Q= y.
Proof. intros. destruct x, y. unfold Q_le, Z_pos__Z, Q_minus, Q_neg, Q_plus, Q_eq.
  assert (forall t: integer, t *Z Z0 =Z= Z0). destruct t. zero.
  assert (forall a b: integer, -Z a *Z b =Z= -Z (a *Z b)).
         destruct a, b. unfold Z_neg, Z_mult, Z_eq. omega.
  rewrite Z_7. rewrite H, H0. rewrite Z_no_diff__eq. rewrite (Z_6 _ i0).
  easy.
Defined.
Lemma Q_pos_diff__gt: forall x y: rational, x - y >Q 0 <-> x >Q y.
Proof. intros. destruct x, y.
  assert (forall t: integer, Z0 *Z t =Z= Z0). destruct t. zero.
  assert (forall a b: integer, -Z a *Z b =Z= -Z (a *Z b)).
         destruct a, b. unfold Z_neg, Z_mult, Z_eq. omega.
  unfold Q_le, Z_pos__Z, Q_minus, Q_neg, Q_plus.
  repeat rewrite H. rewrite Z_8_0.
  repeat rewrite H1. rewrite H0, H0. rewrite Z_pos_diff__gt.
  repeat rewrite Z_5. simpl. zero. one. easy.
Defined.
Lemma Q_10_0: forall x: rational,
    (  x <Q 0 /\ ~ x =Q= 0 /\ ~ x >Q 0) \/
    (~ x <Q 0 /\   x =Q= 0 /\ ~ x >Q 0) \/
    (~ x <Q 0 /\ ~ x =Q= 0 /\   x >Q 0).
Proof.
  intros [ix rx]. repeat rewrite Q_le_iff_neg; repeat rewrite Q_le_iff_pos; repeat rewrite Q_eq_iff.
  assert (Q_numerator (ix // rx) =Z= ix) by reflexivity. rewrite H.
  apply Z_10.
Defined.

(** trichotomy *)
Theorem Q_10: forall x y: rational,
  (  x <Q y /\ ~ x =Q= y /\ ~ x >Q y) \/
  (~ x <Q y /\   x =Q= y /\ ~ x >Q y) \/
  (~ x <Q y /\ ~ x =Q= y /\   x >Q y).
Proof.
  intros. rewrite <- Q_neg_diff__lt. rewrite <- Q_no_diff__eq. rewrite <- (Q_pos_diff__gt x y).
  apply Q_10_0.
Defined.

(** trichotomy *)
Corollary Q_10_1: forall x y: rational, x <Q y \/ x =Q= y \/ x >Q y.
Proof.
  intros.
  pose proof (Q_10 x y).
  destruct H; destruct H.
  - left. apply H.
  - destruct H. destruct H0. right. left. apply H0.
  - destruct H. destruct H0. right. right. apply H1.
Defined.

(** transitivity *)
Theorem Q_11: forall x y z: rational, x <Q y -> y <Q z -> x <Q z.
Proof. intros x y z. rewrite <- (Q_neg_diff__lt x y). rewrite <- (Q_neg_diff__lt x z). rewrite <- (Q_neg_diff__lt y z).
  assert (forall a b: rational, a <Q 0 -> b <Q 0 -> a + b <Q 0).
  { destruct a, b. repeat rewrite Q_le_iff_pos. unfold Q_plus. unfold Q_numerator.
    destruct i, i0. unfold Z_pos__Z, Z_mult. zero. simpl.
    rewrite (N_cons_le_mult_pos (proj1_sig z1) n0 n).
    rewrite (N_cons_le_mult_pos (proj1_sig z0) n2 n1).
    rewrite (mult_comm _ n), (mult_comm _ n0), (mult_comm _ n1), (mult_comm _ n2).
    repeat rewrite N_nle__gt.
    assert (forall k l m n: nat, k > l -> m > n -> k + m > l + n).
    intros. omega.
    apply H.
    destruct z0. unfold gt. rewrite <- N_ltb_true__lt. apply i.
    destruct z1. unfold gt. rewrite <- N_ltb_true__lt. apply i. }
  assert ((x - y) + (y - z) =Q= x - z).
  { destruct x, y, z. unfold Q_minus, Q_neg.
    rewrite Q_1. rewrite <- (Q_1 (-Z i0 // z1)).
    assert (- (i0 // z1) + (i0 // z1) =Q= 0).
    rewrite Q_2. apply Q_4.
    unfold Q_neg in H0.
    rewrite H0.
    assert (forall q: rational, 0 + q =Q= q).
    destruct q as [q q']. unfold Q_plus.
    assert (forall z: integer, Z0 +Z z =Z= z).
    destruct z2. simpl. omega.
    unfold Q_eq. rewrite H1. rewrite Z_7. unfold Z_pos__Z. rewrite Z_pos_mult_compat.
    rewrite Z_6. assert ((Z_pos__N ZP1 * Z_pos__N q')%nat = proj1_sig q') by zero.
    rewrite H2. reflexivity.
    rewrite H1. reflexivity. }
  intros. rewrite <- H0. apply (H (x - y) (y - z)). apply H1. apply H2. Defined.

(** addition preserves the order *)
Theorem Q_12: forall x y z: rational, x <Q y -> x + z <Q y + z.
Proof. intros x y z. rewrite <- Q_pos_diff__gt. destruct x, y, z. simpl.
  rewrite Z_7.
  assert (forall a b: integer, a +Z -Z b =Z= a -Z b).
         destruct a, b. unfold Z_neg, Z_plus, Z_minus. reflexivity.
  assert (forall a b: integer, -Z a *Z b =Z= -Z (a *Z b)).
         destruct a, b. unfold Z_neg, Z_mult, Z_eq. omega.
  rewrite H0, H. unfold Z_minus.
  rewrite Z_pos_diff__gt.
  assert (forall j k: Z_pos, Z_pos__Z (Z_pos_mult j k) =Z= Z_pos__Z j *Z Z_pos__Z k).
  intros; unfold Z_pos__Z, Z_mult. rewrite Z_pos_mult_compat. zero.
  repeat rewrite H1. repeat rewrite <- Z_5. intros.
  apply Z_13.
  repeat rewrite Z_8_0.
  rewrite Z_5. rewrite (Z_6 (Z_pos__Z z)). rewrite <- Z_5.
  apply (Z_13 _ _ (Z_pos__Z z)) in H2.
  apply (Z_12 _ _ (i1 *Z Z_pos__Z z1 *Z Z_pos__Z z0)) in H2.
  repeat rewrite (Z_5 _ _ (Z_pos__Z z1)).
  rewrite (Z_6 (Z_pos__Z z) (Z_pos__Z z1)), (Z_6 (Z_pos__Z z0) (Z_pos__Z z1)).
  repeat rewrite <- Z_5.
  apply H2.
  destruct z. simpl. unfold is_true in i2. rewrite N_ltb_true__lt in i2. omega.
  destruct z. simpl. unfold is_true in i2. rewrite N_ltb_true__lt in i2. omega.
Defined.

Theorem Q_13:
Theorem Q_14:






Theorem Q_16: forall q: rational, - q =Q= (-Z Q_numerator q // Q_denominator q). 
Proof. intros. destruct q. simpl. destruct i. simpl. zero. simpl. 
  rewrite plus_comm. rewrite (mult_comm _ n), (mult_comm _ n0). reflexivity.
Defined.

(* 
Theorem Q_17: trichotomy *)













