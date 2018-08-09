Require Import Coq.omega.Omega.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import logic.
Require Import natural.
Require Import integer.
Require Import Z_nonzero.

Delimit Scope rational_scope with rational.
Open Scope rational_scope.

Inductive rational: Type :=
| prerat : integer -> Z_nonzero -> rational.

Notation "( x '//' y )" := (prerat x y).

(** zero and one *)
Notation "'0'" := (Z0 // ZN1) : rational_scope.
Notation "'Q0'" := (Z0 // ZN1) : type_scope.
Notation "'1'" := (Z1 // ZN1) : rational_scope.
Notation "'Q1'" := (Z1 // ZN1) : type_scope.

(** natural order for Q *)
Definition Q_le (p q: rational) := (** p <= q iff *)
match p with
| (p1 // p2) =>
  match q with
  | (q1 // q2) => (p1 *Z (Z_nonzero__Z p2) *Z ((Z_nonzero__Z q2) *Z (Z_nonzero__Z q2))) <=Z ((Z_nonzero__Z p2) *Z (Z_nonzero__Z p2) *Z (q1 *Z (Z_nonzero__Z q2)))
  end
end.

Lemma Q_le_refl: Reflexive Q_le.
Proof. unfold Reflexive. intros. destruct x as [i [z e]]; simpl. rewrite Z_6. apply Z_le_refl. Defined.

Lemma Q_le_tran: Transitive Q_le.
Proof. unfold Transitive. intros. destruct x as [xi [xz xe]], y as [yi [yz ye]], z as [zi [zz ze]]; simpl in H, H0.
  unfold Q_le; simpl. rewrite (Z_13_1 _ _ (zz *Z zz)) in H. rewrite (Z_5 (xz *Z xz)) in H.
  rewrite (Z_13_1 _ _ (xz *Z xz)) in H0. rewrite (Z_6 _ (xz *Z xz)) in H0. rewrite H0 in H.
  rewrite (Z_5 (yz *Z yz)) in H. rewrite (Z_6 (yz *Z yz)) in H. rewrite (Z_6 _ (xz *Z xz)) in H.
  rewrite (Z_5 (xi *Z xz)) in H. rewrite (Z_6 (yz *Z yz)) in H. rewrite <- Z_5 in H.
  rewrite <- (Z_13_1 _ _ (yz *Z yz)) in H.
  apply H.

  pose proof (Z_square__nonneg yz). rewrite Z_10_3 in H1. destruct H1. apply H1. destruct yz. symmetry in H1. rewrite Z_zero_square in H1. contradiction.
  pose proof (Z_square__nonneg xz). rewrite Z_10_3 in H1. destruct H1. apply H1. destruct xz. symmetry in H1. rewrite Z_zero_square in H1. contradiction.
  pose proof (Z_square__nonneg zz). rewrite Z_10_3 in H1. destruct H1. apply H1. destruct zz. symmetry in H1. rewrite Z_zero_square in H1. contradiction.
Defined.

Add Parametric Relation:
  rational Q_le
  reflexivity proved by Q_le_refl
  transitivity proved by Q_le_tran
  as Q_le_rel.

Notation "z '<=Q' w" := (Q_le z w) (at level 70, no associativity) : type_scope.
Notation "z '<Q' w" := (~ Q_le w z) (at level 70, no associativity) : type_scope.
Notation "z '>=Q' w" := (Q_le w z) (at level 70, no associativity) : type_scope.
Notation "z '>Q' w" := (~ Q_le z w) (at level 70, no associativity) : type_scope.

Definition Q_eq (p q: rational): Prop :=
match p with
| (p1 // p2) =>
  match q with
  | (q1 // q2) => (p1 *Z (Z_nonzero__Z q2)) =Z= ((Z_nonzero__Z p2) *Z q1)
  end
end.

Notation "p =Q= q" := (Q_eq p q) (at level 70): type_scope.
Notation "p <Q> q" := (~ p =Q= q) (at level 70): type_scope.

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
  destruct rx as [rx ex]; destruct ry as [ry ey]; destruct rz as [rz ez]; simpl; simpl in H, H0.
  rewrite (Z_cons_eq_mult _ _ ry).
  rewrite (Z_6 rx iz). rewrite <- (Z_5 ry iz rx). rewrite <- H0.
  rewrite Z_5. rewrite (Z_6 rz rx). repeat rewrite <- Z_5. repeat rewrite (Z_6 _ rz).
  rewrite <- (Z_cons_eq_mult _ _ rz). now rewrite (Z_6 ry ix), (Z_6 iy rx).
  apply ez. apply ey.
Defined.

Add Parametric Relation:
  rational Q_eq
  reflexivity proved by Q_refl
  symmetry proved by Q_symm
  transitivity proved by Q_tran
  as Q.

Instance Q_eq_le_subrel: subrelation Q_eq Q_le.
Proof. unfold subrelation. destruct x, y. unfold Q_le. intros. unfold Q_eq in H.
  assert (Z_nonzero__Z z *Z Z_nonzero__Z z *Z (i0 *Z Z_nonzero__Z z0) =Z= 
    i *Z Z_nonzero__Z z *Z (Z_nonzero__Z z0 *Z Z_nonzero__Z z0)).
  repeat rewrite Z_5. rewrite (Z_6 (Z_nonzero__Z z) (Z_nonzero__Z z0 *Z Z_nonzero__Z z0)).
  repeat rewrite <- Z_5. rewrite H. rewrite (Z_5 (Z_nonzero__Z z) i0). rewrite (Z_5 _ (i0 *Z Z_nonzero__Z z0)).
  rewrite (Z_6 (i0 *Z Z_nonzero__Z z0)). repeat rewrite <- Z_5. reflexivity.
  rewrite H0. easy.
Defined.

Instance Q_eq_ge_subrel: subrelation Q_eq (fun x y => x >=Q y).
Proof. unfold subrelation. intros. symmetry in H. rewrite H. easy.
Defined.

Instance Q_lt_le_subrel: subrelation (fun x y => x <Q y) Q_le.
Proof. unfold subrelation. destruct x, y. unfold Q_le. intros.
  rewrite (Z_6 (i0 *Z Z_nonzero__Z z0)) in H. rewrite (Z_6 _ (i *Z Z_nonzero__Z z)) in H.
  apply Z_lt_le_subrel. apply H.
Defined.

Instance Q_gt_ge_subrel: subrelation (fun x y => x >Q y) (fun x y => x >=Q y).
Proof. unfold subrelation. destruct x, y. unfold Q_le. intros.
  rewrite (Z_6 (i0 *Z Z_nonzero__Z z0)). rewrite (Z_6 _ (i *Z Z_nonzero__Z z)).
  apply Z_lt_le_subrel. apply H.
Defined.

Add Parametric Morphism: Q_le with signature Q_eq ++> Q_eq ++> iff as Q_le_compat_morph.
Proof. intros. destruct x, y, x0, y0. unfold Q_eq in H, H0. unfold Q_le.
Admitted.

Definition Q_leb (p q: rational): bool := (** p <= q iff *)
match p with
| (p1 // p2) =>
  match q with
  | (q1 // q2) => (p1 *Z (Z_nonzero__Z p2) *Z ((Z_nonzero__Z q2) *Z (Z_nonzero__Z q2))) <=Z? ((Z_nonzero__Z p2) *Z (Z_nonzero__Z p2) *Z (q1 *Z (Z_nonzero__Z q2)))
  end
end.

Definition Q_ltb (p q: rational): bool :=
match p with
| (p1 // p2) =>
  match q with
  | (q1 // q2) => (p1 *Z (Z_nonzero__Z p2) *Z ((Z_nonzero__Z q2) *Z (Z_nonzero__Z q2))) <Z? ((Z_nonzero__Z p2) *Z (Z_nonzero__Z p2) *Z (q1 *Z (Z_nonzero__Z q2)))
  end
end.

Definition Q_eqb (p q: rational): bool :=
match p with
| (p1 // p2) =>
  match q with
  | (q1 // q2) => (Z_mult p1 (Z_nonzero__Z q2)) =Z=? (Z_mult (Z_nonzero__Z p2) q1)
  end
end.

Notation "z '<=Q?' w" := (Q_leb z w) (at level 70, no associativity) : type_scope.
Notation "z '<Q?' w" := (Q_ltb z w) (at level 70, no associativity) : type_scope.
Notation "z '>=Q?' w" := (Q_leb w z) (at level 70, no associativity) : type_scope.
Notation "z '>Q?' w" := (Q_ltb w z) (at level 70, no associativity) : type_scope.
Notation "z '=Q=?' w" := (Q_eqb w z) (at level 70, no associativity) : type_scope.

Add Parametric Morphism: Q_leb with signature Q_eq ++> Q_eq ++> eq as Q_leb_morph.
Proof. intros. destruct x, y, x0, y0. unfold Q_eq in H, H0. unfold Q_leb.
Admitted.

Add Parametric Morphism: Q_ltb with signature Q_eq ++> Q_eq ++> eq as Q_ltb_morph.
Proof. intros. destruct x, y, x0, y0. unfold Q_eq in H, H0. unfold Q_ltb.
Admitted.

Lemma Q_leb_true__le: forall x y: rational, Q_leb x y = true <-> x <=Q y.
Proof. intros. destruct x, y. simpl. apply Z_leb_true__le. Defined.
Lemma Q_ltb_true__lt: forall x y: rational, Q_ltb x y = true <-> x <Q y. 
Proof. intros. destruct x, y. simpl. rewrite (Z_6 (i0 *Z Z_nonzero__Z z0)), (Z_6 (i *Z Z_nonzero__Z z)). apply Z_ltb_true__lt. Defined.
Lemma Q_eqb_true__eq: forall x y: rational, (Q_eqb x y) = true <-> x =Q= y.
Proof. Admitted.
Lemma Q_leb_false__gt: forall x y: rational, Q_leb x y = false <-> x >Q y.
Proof. intros. destruct x, y. simpl. apply Z_leb_false__gt. Defined.
Lemma Q_ltb_false__ge: forall x y: rational, Q_ltb x y = false <-> x >=Q y.
Proof. intros. destruct x, y. simpl. rewrite (Z_6 (i0 *Z Z_nonzero__Z z0)), (Z_6 (i *Z Z_nonzero__Z z)). apply Z_ltb_false__ge. Defined.
Lemma Q_eqb_false__eq: forall x y: rational, (Q_eqb x y) = false <-> x <Q> y.
Proof. Admitted.

Definition Q_max (z w: rational) :=
if Q_leb z w then w else z.

Add Parametric Morphism: Q_max with signature Q_eq ==> Q_eq ==> Q_eq as Q_max_morph.
Proof. intros. unfold Q_max, Q_eq.
  remember (x0 >=Q? x) as b; destruct b; symmetry in Heqb.
  rewrite H, H0 in Heqb. rewrite Heqb. destruct x0, y0. apply H0.
  rewrite H, H0 in Heqb. rewrite Heqb. destruct x, y. apply H.
Defined.

Fixpoint Q_seq_max (a: nat -> rational) (m: nat) : rational := (* max_{i in 0..m} a i *)
match m with
| 0%nat => (a 0%nat)
| S m' => Q_max (a m) (Q_seq_max a m')
end.

Add Parametric Morphism: Q_seq_max with signature (fun a => fun b => forall n, a n =Q= b n) ==> eq ==> Q_eq as Q_seq_max_morph.
Proof. intros. unfold Q_eq. induction y0.
  simpl. pose proof (H 0%nat) as H0. destruct (x 0%nat), (y 0%nat). apply H0.
  pose proof (H (S y0)) as H0. simpl. unfold Q_max.
  remember (Q_seq_max x y0) as m. remember (Q_seq_max y y0) as n.
  assert (m =Q= n). destruct m, n. apply IHy0.
  remember (m >=Q? x (S y0)) as b; destruct b.
  rewrite H1, H0 in Heqb. rewrite <- Heqb. apply H1.
  rewrite H1, H0 in Heqb. rewrite <- Heqb. apply H0.
Defined.

Theorem Q_seq_max_ge: forall (a: nat -> rational) (m: nat) (n: nat), n <= m -> (Q_seq_max a m) >=Q a n.
Proof. Admitted.

Definition Q_plus (p q: rational) :=
  match p with
  | (ip // rp) =>
    match q with
    | (iq // rq) => ((ip *Z Z_nonzero__Z rq +Z iq *Z Z_nonzero__Z rp) // Z_nonzero_mult rp rq)
    end
  end.

Add Parametric Morphism: Q_plus with signature Q_le ++> Q_le ++> Q_le as Q_le_plus_morph.
Proof. Admitted.

Add Parametric Morphism: Q_plus with signature (fun x y => x <Q y) ++> (fun x y => x <Q y) ++> (fun x y => x <Q y) as Q_lt_plus_morph.
Proof. intros. destruct x as [x1 [x2 x3]], y as [y1 [y2 y3]], x0 as [z1 [z2 z3]], y0 as [w1 [w2 w3]].
  simpl. simpl in H, H0. rewrite <- Z_pos_diff__gt.
Admitted.

Add Parametric Morphism: Q_plus with signature Q_le ++> (fun x y => x <Q y) ++> (fun x y => x <Q y) as Q_le_lt_plus_morph.
Proof. Admitted.

Add Parametric Morphism: Q_plus with signature (fun x y => x <Q y) ++> Q_le ++> (fun x y => x <Q y) as Q_lt_le_plus_morph.
Proof. Admitted.

Add Morphism Q_plus with signature Q_eq ==> Q_eq ==> Q_eq as Q_plus_morph.
Proof. (* well-definedness of Q_plus *)
(* 기존 코드 
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
*)
Admitted.

Notation "p '+' q" := (Q_plus p q) (at level 50, left associativity) : rational_scope.
Notation "p '+Q' q" := (Q_plus p q) (at level 50, left associativity) : type_scope.

(** negation of a rational number: q |-> -q *)
Definition Q_neg (q: rational) :=
  match q with
  | (iq // rq) => (-Z iq // rq)
  end.

Add Parametric Morphism: Q_neg with signature Q_le --> Q_le as Q_le_neg_morph.
Proof. Admitted.

Add Morphism Q_neg with signature Q_eq ==> Q_eq as Q_neg_morph.
Proof. (* well-definedness of Q_neg *)
  destruct x as [[x1 x2] [[x3 x4] x5]], y as [[y1 y2] [[y3 y4] y5]].
  simpl. intros. omega.
Defined.

Notation "'-' q" := (Q_neg q) (at level 35, right associativity) : rational_scope.
Notation "'-Q' q" := (Q_neg q) (at level 35, right associativity) : type_scope.

(** subtraction *)

Definition Q_minus (p q: rational) := p + -q.

Add Parametric Morphism: Q_minus with signature Q_le ++> Q_le --> Q_le as Q_le_minus_morph.
Proof. Admitted.

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
    | (iq // rq) => (ip *Z iq // Z_nonzero_mult rp rq)
    end
  end.

Add Morphism Q_mult with signature Q_eq ==> Q_eq ==> Q_eq as Q_mult_morph.
Proof. (* well-definedness of Z_minus *)
  destruct x as [[x1 x2] [[x3 x4] x5]], y as [[y1 y2] [[y3 y4] y5]], x0 as [[z1 z2] [[z3 z4] z5]], y0 as [[w1 w2] [[w3 w4] w5]].
  simpl. simpl in H.
(* 기존 코드
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
*)
Admitted.

Notation "p '*' q" := (Q_mult p q) (at level 40, left associativity) : rational_scope.
Notation "p '*Q' q" := (Q_mult p q) (at level 40, left associativity) : type_scope.

(* CAUTION: the following two functions are NOT morphisms! (not well-defined) *)
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
  unfold is_true in q4.
Admitted.

Lemma Q_nonzero__iff: forall q: rational, q <Q> 0 <-> Q_numerator q <Z> Z0.
Proof.
  intros. rewrite Q_zero_iff. reflexivity.
Defined.

Definition Q_nonzero: Set := {q : rational | Q_numerator q <Z> Z0}.

(*
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

Definition N_abs_diff (n m: nat) := ((n - m) + (m - n))%nat.

Lemma N_abs_diff_pos: forall q1 q2: nat, q1 <> q2 -> (0 <? N_abs_diff q1 q2) = true.
Proof.
  intros. unfold N_abs_diff. rewrite N_trichotomy_ne in H. rewrite N_ltb_true__lt. destruct H; omega.
Defined.
*)

(** reciprocal of a rational number: q |-> -q *)
Definition Q_recip (q: Q_nonzero): Q_nonzero.
  destruct q as [[q1 [q2 q3]] q4]. simpl in q4.

  exists ( q2 // (exist _ q1 q4) ).
  simpl. apply q3.
Defined.

Definition Q_nonzero_eq (p q: Q_nonzero): Prop := (proj1_sig p) =Q= (proj1_sig q).

Add Morphism Q_recip with signature Q_nonzero_eq ==> Q_nonzero_eq as Q_recip_morph.
Proof. (* well-definedness of Q_recip *)
  destruct x as [[[x1 x2] [[x3 x4] x5]] x6], y as [[[y1 y2] [[y3 y4] y5]] y6].
  simpl in x5, y5.
  unfold Q_nonzero_eq. intros. simpl in H.
  unfold Q_recip; simpl. omega.
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
  destruct x, x0. simpl.
  simpl in n, n0.
  unfold not. intro.
  apply Z_9 in H. destruct H;
  contradiction.
Defined.

Lemma Q_nonzero_mult_compat:
forall p q: Q_nonzero, proj1_sig (Q_nonzero_mult p q) =Q= proj1_sig p *Q proj1_sig q.
Proof. now intros [x xnz] [y ynz]. Defined.

Definition QN1: Q_nonzero.
  refine (exist  _ 1 _). easy.
Defined.
Definition QN2: Q_nonzero.
  refine (exist  _ (1 + 1) _). easy.
Defined.
Definition QN3: Q_nonzero.
  refine (exist  _ (1 + 1 + 1) _). easy.
Defined.
Definition QN4: Q_nonzero.
  refine (exist  _ (1 + 1 + 1 + 1) _). easy.
Defined.

Notation "'/' q" := (Q_recip q) (at level 35, right associativity) : rational_scope.
Notation "'/Q' q" := (Q_recip q) (at level 35, right associativity) : type_scope.

Notation "p '/' q" := (p * proj1_sig (Q_recip q)) (at level 40, left associativity) : rational_scope.
Notation "p '/Q' q" := (p * proj1_sig (Q_recip q)) (at level 40, left associativity) : type_scope.

Theorem Q_1: forall p q r: rational, p + q + r =Q= p + (q + r).
Proof. intros. destruct p, q, r. unfold Q_plus.
  assert (Z_nonzero__Z (Z_nonzero_mult (Z_nonzero_mult z z0) z1) =Z= Z_nonzero__Z (Z_nonzero_mult z (Z_nonzero_mult z0 z1))).
  destruct z, z0, z1. simpl. apply Z_5.
  assert ((i *Z Z_nonzero__Z z0 +Z i0 *Z Z_nonzero__Z z) *Z Z_nonzero__Z z1 +Z i1 *Z Z_nonzero__Z (Z_nonzero_mult z z0)
          =Z= i *Z Z_nonzero__Z (Z_nonzero_mult z0 z1) +Z (i0 *Z Z_nonzero__Z z1 +Z i1 *Z Z_nonzero__Z z0) *Z Z_nonzero__Z z).
  repeat rewrite Z_8_0.
    assert (forall a b: Z_nonzero, Z_nonzero__Z (Z_nonzero_mult a b) =Z= Z_nonzero__Z a *Z Z_nonzero__Z b).
    intros. unfold Z_nonzero__Z. rewrite Z_nonzero_mult_compat. unfold Z_mult. zero.
  repeat rewrite H0. rewrite (Z_6 (Z_nonzero__Z z)). rewrite (Z_5 i0 (Z_nonzero__Z z)). rewrite (Z_6 (Z_nonzero__Z z)).
  repeat rewrite <- Z_5. rewrite <- Z_1. reflexivity.
  unfold Q_eq. rewrite H, H0. rewrite (Z_6 (Z_nonzero__Z (Z_nonzero_mult z (Z_nonzero_mult z0 z1)))). reflexivity.
Defined.

Theorem Q_2: forall p q: rational, p + q =Q= q + p.
Proof. intros. destruct p, q. unfold Q_plus. unfold Q_eq.
  unfold Z_nonzero__Z. rewrite Z_nonzero_mult_compat. rewrite Z_8, Z_8_0. unfold Z_nonzero__Z. rewrite Z_nonzero_mult_compat.
  rewrite (Z_6 (i *Z proj1_sig z0)), (Z_6 (i0 *Z proj1_sig z)).
  rewrite (Z_6 (Z_nonzero__Z z0)).
  apply Z_2.
Defined.

Theorem Q_3: forall q: rational, q + 0 =Q= q.
Proof. intros. destruct q. unfold Q_plus. unfold Q_eq. rewrite Z_7_1. rewrite Z_3. rewrite (Z_6 _ i).
  unfold Z_nonzero__Z. rewrite Z_5. rewrite Z_nonzero_mult_compat. destruct i, z as [[z1 z2] z3].
  simpl. zero. simpl. repeat rewrite mult_1_r. omega. 
Defined.

Theorem Q_4: forall q: rational, q - q =Q= 0.
Proof. intros. destruct q as [i [z1 z2]]. simpl.
  rewrite Z_mult_neg. rewrite Z_7, Z_4, Z_7_0. reflexivity.
Defined.

Theorem Q_5: forall p q r: rational, p * q * r =Q= p * (q * r).
Proof. intros. destruct p as [p1 [p2 p3]], q as [q1 [q2 q3]], r as [r1 [r2 r3]]. simpl.
  rewrite (Z_6 (p1 *Z q1 *Z r1)). repeat rewrite Z_5. reflexivity.
Defined.

Theorem Q_6: forall p q: rational, p * q =Q= q * p.
Proof. intros. destruct p as [p1 [p2 p3]], q as [q1 [q2 q3]]. simpl.
  rewrite (Z_6 (p1 *Z q1)), (Z_6 p1), (Z_6 p2). reflexivity.
Defined.

Theorem Q_7: forall q: rational, q * 1 =Q= q.
Proof. intros. destruct q as [q1 [q2 q3]]. simpl.
  repeat rewrite Z_7. now apply Z_6.
Defined.

Theorem Q_7_0: forall q: rational, q * 0 =Q= 0.
Proof. intros. destruct q as [q1 [q2 q3]]. simpl.
  repeat rewrite Z_7, Z_7_0. reflexivity.
Defined.

Theorem Q_7_1: forall q: rational, 0 * q =Q= 0.
Proof. intros. destruct q as [q1 [q2 q3]]. simpl.
  repeat rewrite Z_7, Z_7_0. destruct q1. reflexivity.
Defined.

Theorem Q_7_2: forall q: rational, q * - Q1 =Q= -q.
Proof. intros. destruct q as [q1 [q2 q3]]. simpl.
  destruct q1, q2. simpl. zero. simpl. one.
  repeat rewrite (mult_comm n1), (mult_comm n2). omega.
Defined.

Theorem Q_7_3: forall q: rational, - Q1 * q =Q= -q.
Proof. intros. rewrite Q_6. apply Q_7_2.
Defined.

Theorem Q_8: forall q: Q_nonzero, Q_nonzero_eq (Q_nonzero_mult q (/q)) (QN1).
Proof. intros. unfold Q_nonzero_eq. simpl. destruct q as [[q1 [q2 q3]] q4]. simpl.
  repeat rewrite Z_7. now apply Z_6.
Defined.

Corollary Q_8_0: forall q: Q_nonzero, proj1_sig (Q_nonzero_mult q (/q)) =Q= 1.
Proof. intros. simpl. destruct q as [[q1 [q2 q3]] q4]. simpl.
  repeat rewrite Z_7. now apply Z_6.
Defined.

Theorem Q_9: forall p q r: rational, p * (q + r) =Q= p * q + p * r.
Proof. intros. destruct p as [p1 [p2 p3]], q as [q1 [q2 q3]], r as [r1 [r2 r3]]. simpl.
  repeat rewrite Z_8. repeat rewrite Z_8_0.
  (* first term *)
  assert (p1 *Z (q1 *Z r2) *Z (p2 *Z q2 *Z (p2 *Z r2)) =Z= p2 *Z (q2 *Z r2) *Z (p1 *Z q1 *Z (p2 *Z r2))).
    rewrite (Z_5 p2 (q2 *Z r2)). rewrite <- (Z_5 (q2 *Z r2)). rewrite (Z_6 (q2 *Z r2)).
    rewrite <- (Z_5 p2). rewrite <- (Z_5 p2). rewrite (Z_6 p2 (p1 *Z q1)).
    rewrite (Z_5 (p1 *Z q1) p2). rewrite <- (Z_5 p2 q2 r2).
    rewrite (Z_6 (p2 *Z q2) r2). repeat rewrite Z_5. reflexivity.

  (* second term *)
  assert (p1 *Z (r1 *Z q2) *Z (p2 *Z q2 *Z (p2 *Z r2)) =Z= p2 *Z (q2 *Z r2) *Z (p1 *Z r1 *Z (p2 *Z q2))).
    rewrite <- (Z_5 (p2 *Z (q2 *Z r2))). rewrite (Z_6 _ (p1 *Z r1)). rewrite <- (Z_5 p2 q2 r2). rewrite (Z_6 p2 q2).
    rewrite (Z_5 q2 p2 r2). rewrite (Z_5 (p1 *Z r1)). rewrite (Z_5 q2 (p2 *Z r2)). rewrite (Z_6 (p2 *Z r2)).
    repeat rewrite Z_5. reflexivity.

  rewrite H, H0. reflexivity.
Defined.

Corollary Q_9_0: forall p q r: rational, (q + r) * p =Q= q * p + r * p.
Proof. intros. repeat rewrite (Q_6 _ p). apply Q_9. Defined.

Corollary Q_mult_neg_distr: forall p q: rational, - (p + q) =Q= -p - q.
Proof. intros. rewrite <- Q_7_3. rewrite Q_9. repeat rewrite Q_7_3. reflexivity. Defined.

Corollary Q_double: forall q: rational, q + q =Q= q * (1 + 1).
Proof. intros. rewrite Q_9. repeat rewrite Q_7. reflexivity. Defined.

Lemma Q_le_iff_nonpos: forall x: rational, x <=Q 0 <-> Q_numerator x *Z Z_nonzero__Z (Q_denominator x) <=Z Z0.
Proof. destruct x as [x1 [x2 x3]]. simpl. rewrite Z_7, Z_7_0. reflexivity.
Defined.

Lemma Q_le_iff_nonneg: forall x: rational, x >=Q 0 <-> Q_numerator x *Z Z_nonzero__Z (Q_denominator x) >=Z Z0.
Proof. destruct x as [[x11 x12] [[x21 x22] x3]]. simpl. zero. Defined.

Lemma Q_eq_iff: forall x: rational, x =Q= 0 <-> Q_numerator x =Z= Z0.
Proof. destruct x as [x1 [x2 x3]]. simpl. rewrite Z_7, Z_7_0. reflexivity.
Defined.

Lemma Q_neg_diff__lt: forall x y: rational, x - y <Q 0 <-> x <Q y.
Proof. Admitted.

Lemma Q_no_diff__eq: forall x y: rational, x - y =Q= 0 <-> x =Q= y.
Proof. Admitted.

Lemma Q_pos_diff__gt: forall x y: rational, x - y >Q 0 <-> x >Q y.
Proof. Admitted.

Theorem Q_cons_lt_plus: forall p q r s: rational, p <Q q -> r <Q s -> p + r <Q q + s.
Proof. Admitted.

Theorem Q_cons_le_plus: forall p q r s: rational, p <=Q q -> r <=Q s -> p + r <=Q q + s.
Proof. Admitted.

Theorem Q_cons_lt_mult_nonneg: forall p q r s: rational, p >=Q 0 -> r >=Q 0 -> p <Q q -> r <Q s -> p * r <Q q * s.
Proof. Admitted.

Theorem Q_cons_le_mult_nonneg: forall p q r s: rational, p >=Q 0 -> r >=Q 0 -> p <=Q q -> r <=Q s -> p * r <=Q q * s.
Proof. Admitted.

Theorem Q_cons_lt_mult_nonneg_0: forall p q r s: rational, p >=Q 0 -> r >=Q 0 -> q >Q 0 -> p <=Q q -> r <Q s -> p * r <Q q * s.
Proof. Admitted.

Lemma Q_10_0: forall x: rational,
    (  x <Q 0 /\ ~ x =Q= 0 /\ ~ x >Q 0) \/
    (~ x <Q 0 /\   x =Q= 0 /\ ~ x >Q 0) \/
    (~ x <Q 0 /\ ~ x =Q= 0 /\   x >Q 0).
Proof. Admitted.

(** trichotomy *)
Theorem Q_10: forall x y: rational,
  (  x <Q y /\ ~ x =Q= y /\ ~ x >Q y) \/
  (~ x <Q y /\   x =Q= y /\ ~ x >Q y) \/
  (~ x <Q y /\ ~ x =Q= y /\   x >Q y).
Proof. Admitted.

(** trichotomy *)
Corollary Q_10_1: forall x y: rational, x <Q y \/ x =Q= y \/ x >Q y.
Proof. Admitted.

(** trichotomy *)
Corollary Q_10_2: forall x: rational, x <Q> 0 <-> x >Q 0 \/ x <Q 0.
Proof. Admitted.

(** transitivity *)
Theorem Q_11: forall x y z: rational, x <Q y -> y <Q z -> x <Q z.
Proof. Admitted.

(** addition preserves the order *)
Theorem Q_12: forall x y z: rational, x <Q y -> x + z <Q y + z.
Proof. Admitted.

Lemma Q_mult_neg: forall v w: rational, - v * w =Q= - (v * w).
Proof. Admitted.

Lemma Q_mult_neg_0: forall v w: rational, v * - w =Q= - (v * w).
Proof. Admitted.

Theorem Q_13: forall p q r: rational, p <Q q -> r >Q 0 -> p * r <Q q * r.
Proof. Admitted.

Corollary Q_13_1: forall p q r: rational, r >Q 0 -> p <Q q <-> p * r <Q q * r.
Proof. Admitted.

Definition Q_abs (q: rational): rational := (Z_abs (Q_numerator q) // Z_nonzero_abs (Q_denominator q)). 

Add Morphism Q_abs with signature Q_eq ==> Q_eq as Q_abs_morph.
Proof. (* well-definedness of Z_minus *)
  assert (forall x1 x2 y1 y2: integer, 
    x2 >Z Z0 -> y2 >Z Z0 -> x1 *Z y2 =Z= x2 *Z y1 -> Z_abs x1 *Z Z_abs y2 =Z= Z_abs x2 *Z Z_abs y1).
    intros x1 x2 y1 y2 H H0.
    assert (x2 >=Z Z0). rewrite Z_10_3. left. apply H.
    assert (y2 >=Z Z0). rewrite Z_10_3. left. apply H0.
    apply Z_abs_nonneg__same in H1; apply Z_abs_nonneg__same in H2.
    rewrite H1, H2.
    pose proof (Z_10_4 x1 Z0). destruct H3.
    (* x1 <=Z Z0 -> y1 <=Z Z0 *)
    intro. assert (y1 <=Z Z0).
      assert (y1 >Z Z0 -> False).
      intro. pose proof ((Z_mult_pos_pos__pos x2 y1) H H5). rewrite <- H4 in H6.
      pose proof (proj1 (Z_13_1 x1 Z0 y2 H0) H3). rewrite Z_7_1 in H7. contradiction.
    rewrite Z_le_double_neg_elim. unfold not. now apply H5.
    apply Z_abs_nonpos__inv in H3; apply Z_abs_nonpos__inv in H5.
    rewrite H3, H5.
    rewrite Z_mult_neg. rewrite Z_mult_neg_0. rewrite H4. reflexivity.
    (* x1 >=Z Z0 -> y1 >=Z Z0 *)
    intro. assert (y1 >=Z Z0).
      assert (y1 <Z Z0 -> False).
      intro. pose proof (proj1 (Z_lt_inv y1 Z0) H5). pose proof ((Z_mult_pos_pos__pos x2 (-Z y1)) H H6).
      rewrite Z_mult_neg_0 in H7. assert (-Z Z0 =Z= Z0) by reflexivity. rewrite <- H8 in H7.
      pose proof (proj2 (Z_lt_inv (x2 *Z y1) Z0) H7). rewrite <- H4 in H9.
      pose proof (proj1 (Z_le_inv Z0 x1) H3). rewrite H8 in H10.
      pose proof (proj1 (Z_13_1 (-Z x1) Z0 y2 H0) H10). rewrite Z_7_1 in H11. rewrite <- H8 in H11.
      rewrite Z_mult_neg in H11. rewrite <- Z_le_inv in H11. contradiction.
    rewrite Z_le_double_neg_elim. unfold not. now apply H5.
    apply Z_abs_nonneg__same in H3; apply Z_abs_nonneg__same in H5.
    rewrite H3, H5. now apply H4.

  destruct x as [x1 [x2 x3]], y as [y1 [y2 y3]]. simpl.
  rewrite Z_10_2 in x3, y3. destruct x3, y3.
  apply H; [apply H0 | apply H1].

  pose proof (proj1 (Z_lt_inv y2 Z0) H1). assert (-Z Z0 =Z= Z0) by reflexivity. rewrite H3 in H2.
  intro. rewrite <- (Z_cons_abs_neg x1), <- (Z_cons_abs_neg y2).
  assert (forall x: integer, -Z (-Z x) =Z= x) by (destruct x; reflexivity).
  rewrite <- H5 in H4. rewrite <- Z_mult_neg in H4. rewrite <- Z_mult_neg_0 in H4.
  apply H. apply H0. apply H2. apply H4.

  pose proof (proj1 (Z_lt_inv x2 Z0) H0). assert (-Z Z0 =Z= Z0) by reflexivity. rewrite H3 in H2.
  intro. rewrite <- (Z_cons_abs_neg x2), <- (Z_cons_abs_neg y1).
  assert (forall x: integer, -Z (-Z x) =Z= x) by (destruct x; reflexivity).
  rewrite <- (H5 (x2 *Z y1)) in H4. rewrite <- Z_mult_neg in H4. rewrite <- Z_mult_neg_0 in H4.
  apply H. apply H2. apply H1. apply H4.

  pose proof (proj1 (Z_lt_inv x2 Z0) H0). pose proof (proj1 (Z_lt_inv y2 Z0) H1). 
  assert (-Z Z0 =Z= Z0) by reflexivity. rewrite H4 in H2, H3.
  intro. rewrite <- (Z_cons_abs_neg x2), <- (Z_cons_abs_neg y2).
  assert (forall a b: integer, a =Z= b -> -Z a =Z= -Z b) by (intros; rewrite H6; reflexivity).
  apply H6 in H5. rewrite <- Z_mult_neg_0 in H5. rewrite <- Z_mult_neg in H5.
  apply H. apply H2. apply H3. apply H5.
Defined.

Theorem Q_abs__nonneg: forall z: rational, Q_abs z >=Q 0.
Proof. Admitted.

Theorem Q_cons_abs_neg: forall q: rational, Q_abs (-q) =Q= Q_abs q.
Proof. destruct q. simpl.
  rewrite Z_cons_abs_neg. apply Z_6.
Defined.

Theorem Q_cons_abs_mult: forall z w: rational, Q_abs (z *Q w) =Q= Q_abs z * Q_abs w.
Proof. Admitted.

Theorem Q_abs_nonneg__same: forall z: rational, z >=Q 0 <-> Q_abs z =Q= z.
Proof. Admitted.

Theorem Q_abs_nonpos__inv: forall z: rational, z <=Q 0 <-> Q_abs z =Q= - z.
Proof. Admitted.

Theorem Q_triangle_ineq: forall p q : rational, Q_abs p +Q Q_abs q >=Q Q_abs (p +Q q).
Proof. Admitted.

Lemma Q_cons_pos_div_QN2: forall epsilon: rational, epsilon >Q Q0 -> epsilon /Q QN2 >Q Q0.
  destruct epsilon. unfold QN2. simpl. rewrite Z_nonzero_mult_compat. simpl.
  repeat rewrite Z_7_0. repeat rewrite Z_7. rewrite <- Z_5.
  assert (i *Z Z_nonzero__Z z *Z (2, 0) =Z= i *Z Z_nonzero__Z z +Z i *Z Z_nonzero__Z z).
    assert ((2, 0) =Z= Z1 +Z Z1) by reflexivity. rewrite H.
  rewrite Z_8. repeat rewrite Z_7. easy. rewrite H. destruct (i *Z Z_nonzero__Z z). simpl. omega.
Defined.

Lemma Q_double_half: forall epsilon: rational, (epsilon /Q QN2) +Q (epsilon /Q QN2) =Q= epsilon.
  intros. rewrite Q_double.
  assert (Q1 +Q Q1 =Q= proj1_sig QN2) by reflexivity.
  rewrite H; clear H. rewrite Q_5.
  assert (proj1_sig (/Q QN2) *Q proj1_sig QN2 =Q= Q1) by apply Q_8_0.
  rewrite H; clear H. apply Q_7.
Defined.

Close Scope rational_scope.
