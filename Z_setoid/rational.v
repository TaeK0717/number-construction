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
Qed.

Theorem Q_symm: Symmetric Q_eq.
Proof.
  (* symmetricity *) unfold Symmetric.
  destruct x, y.
  unfold Q_eq.
  intros.
  symmetry.
  rewrite (Z_6 _ i), (Z_6 i0 _).
  apply H.
Qed.

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
Qed.

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
Qed.

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
Qed.

Notation "'-' q" := (Q_neg q) (at level 35, right associativity) : rational_scope.
Notation "'-Q' q" := (Q_neg q) (at level 35, right associativity) : type_scope.

(** subtraction *)

Definition Q_minus (p q: rational) := p + -q.

Add Morphism Q_minus with signature Q_eq ==> Q_eq ==> Q_eq as Q_minus_morph.
Proof. (* well-definedness of Z_minus *)
  unfold Q_minus. intros. now rewrite H, H0.
Qed.

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
Admitted.

Notation "p '*' q" := (Q_mult p q) (at level 40, left associativity) : rational_scope.
Notation "p '*Q' q" := (Q_mult p q) (at level 40, left associativity) : type_scope.

Definition Q_nonzero: Set := {q : rational | q <Q> 0}.

Definition Q_numerator (q: rational) :=
  match q with
  | (iq // rq) => iq
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
Qed.

Lemma Q_nonzero__iff: forall q: rational, q <Q> 0 <-> Q_numerator q <Z> Z0.
Proof.
  intros. rewrite Q_zero_iff. reflexivity.
Qed.

Definition N_sgn_diff__Z (n m: nat): integer :=
  if n <? m then Z1 else if n =? m then Z0 else -Z Z1.

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
Qed.

Lemma N_abs_diff: forall q1 q2: nat, q1 <> q2 -> 0 < q1 - q2 + (q2 - q1).
Proof.
  intros. rewrite N_trichotomy_diff in H. destruct H; omega.
Qed.

(** reciprocal of a rational number: q |-> -q *)
Definition Q_recip (q: Q_nonzero): Q_nonzero.
  destruct q as [[[q1 q2] [q3 q4]] Hq].
  simpl in Hq.
  remember ((q1 - q2) + (q2 - q1))%nat as d.
  repeat rewrite mult_1_r in Hq; repeat rewrite mult_0_r in Hq; repeat rewrite <- plus_n_O in Hq; simpl in Hq.
  remember (fun x => (0 <? x) = true) as f.
  assert ((0 <? d) = true).
  { apply Nat.ltb_lt. rewrite N_trichotomy_diff in Hq. destruct Hq; omega. }
  remember (exist (fun x => (0 <? x) = true) d H) as m.
  exists ( ((N_sgn_diff__Z q1 q2) *Z (q3, 0)) // m ).

  assert ((q1, q2) <Z> Z0). { simpl. repeat rewrite plus_0_r. apply Hq. }
  rewrite Q_nonzero__iff.
  simpl.
  rewrite N_trichotomy_diff in Hq.

  assert (forall z w: integer, z <Z> Z0 /\ w <Z> Z0 -> z *Z w <Z> Z0). {
    intros [z1 z2] [w1 w2]. simpl. repeat rewrite plus_0_r. intros. destruct H1.
    rewrite N_trichotomy_diff in H1; rewrite N_trichotomy_diff in H2; rewrite N_trichotomy_diff.
    destruct H1, H2.
    - left. rewrite (plus_comm (z1 * w1)), (plus_comm (z1 * w2)). apply N_rearr.
      split; [apply H1 | apply H2].
    - right. rewrite (plus_comm (z1 * w2)), (plus_comm (z1 * w1)). apply N_rearr.
      split; [apply H1 | apply H2].
    - right. apply N_rearr.
      split; [apply H1 | apply H2].
    - left. apply N_rearr.
      split; [apply H1 | apply H2].
  }
  apply H1. split.
  assert (forall a b: nat, a > b -> (a <? b) = false /\ (a =? b) = false).
  { induction a. intros. inversion H2. intros. destruct b. split; unfold Nat.ltb; reflexivity.
  assert (S a > S b -> a > b) by omega. apply H3 in H2.
  apply IHa in H2. destruct H2.
  split. unfold Nat.ltb. unfold Nat.ltb in H2.
  rewrite N_leb_false_gt. rewrite N_leb_false_gt in H2. omega.
  rewrite N_beq_false. rewrite N_beq_false in H4. omega.
  }

  unfold N_sgn_diff__Z.

  unfold is_true in q4.
  rewrite Nat.ltb_lt in q4.
  simpl in H0. repeat rewrite <- plus_n_O in H0. destruct Hq.

  apply Z_sgn_diff__nonzero. apply H0.
  apply Z_sgn_diff__nonzero. apply H0.
  simpl. unfold is_true in q4. rewrite Nat.ltb_lt in q4. omega.
Defined.

Definition Q_nonzero_eq (p q: Q_nonzero): Prop := (proj1_sig p) =Q= (proj1_sig q).

Add Morphism Q_recip with signature Q_nonzero_eq ==> Q_nonzero_eq as Q_recip_morph.
Proof. (* well-definedness of Q_recip *)
  destruct x as [[[x1 x2] [x3 x4]] x5], y as [[[y1 y2] [y3 y4]] y5].
  unfold Q_nonzero_eq. intros. simpl in H. unfold Q_recip. 
  simpl. unfold N_sgn_diff__Z.
  simpl in x5, y5.
  assert (mult_1_r: forall n:nat, (n * 1)%nat = n) by (intros; omega).
  repeat rewrite mult_1_r in x5; repeat rewrite mult_0_r, plus_0_r in x5; simpl in x5.
  intros.
  repeat rewrite mult_1_r in H; repeat rewrite mult_0_r in H; repeat rewrite plus_0_r in H; simpl in H.
  assert (y1 <> y2).
  pose proof y5 as y6.
  repeat rewrite mult_1_r in y6; repeat rewrite mult_0_r in y6; repeat rewrite plus_0_r in y6; simpl in y6.
  apply y6.
  pose proof (N_abs_diff y1 y2) as NDy.
  apply NDy in H0.
  rewrite <- Nat.ltb_lt in H0.
  unfold Z_eq.
  rewrite H0.
  
Qed.

Notation "'/' q" := (Q_neg q) (at level 35, right associativity) : rational_scope.
Notation "'/Q' q" := (Q_neg q) (at level 35, right associativity) : type_scope.





















