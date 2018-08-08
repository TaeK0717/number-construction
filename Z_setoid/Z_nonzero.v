From Coq Require Import Arith.
Require Import logic.
Require Import natural.
Require Import integer.
Require Import ProofIrrelevance.

Local Coercion is_true : bool >-> Sortclass.

Definition Z_nonzero: Set := {m : integer | negb (Z_eqb m Z0) }.

Definition Z_nonzero__Z (p: Z_nonzero): integer := proj1_sig p.

Definition Z_nonzero_mult : Z_nonzero -> Z_nonzero -> Z_nonzero.
  intros [x xnz] [y ynz].
  refine (exist  _ (x *Z y) _).
  unfold is_true in xnz, ynz.
  rewrite <- negb_true in xnz, ynz.
  destruct x, y.
  unfold Z_eqb in xnz, ynz. rewrite N_eqb_false__ne in xnz, ynz.
  zero_in xnz; zero_in ynz.
  unfold is_true.
  rewrite <- negb_true.
  unfold Z_eqb. simpl. zero.
  rewrite N_eqb_false__ne.
  rewrite N_trichotomy_ne.
  rewrite N_trichotomy_ne in xnz, ynz.
  destruct xnz; destruct ynz.
  - right. apply N_rearrange; [apply H | apply H0].
  - left. apply N_rearrange; [apply H | apply H0].
  - left. unfold gt in H. rewrite (plus_comm (n * n1)), (plus_comm (n * n2)).
    apply N_rearrange; [apply H | apply H0].
  - right. unfold gt in H, H0. unfold gt. rewrite (plus_comm (n * n1)), (plus_comm (n * n2)).
    apply N_rearrange; [apply H | apply H0].
Defined.

Lemma Z_nonzero_mult_compat:
forall p q: Z_nonzero, Z_nonzero__Z (Z_nonzero_mult p q) = Z_nonzero__Z p *Z Z_nonzero__Z q.
Proof. now intros [x xnz] [y ynz]. Defined.

Definition ZN1: Z_nonzero.
  refine (exist  _ Z1 _). easy.
Defined.

Lemma Z_nonzero__Z_injective:
  forall t1 t2: Z_nonzero, Z_nonzero__Z t1 = Z_nonzero__Z t2 -> t1 = t2.
Proof.
  intros [x1 i1] [x2 i2]; simpl; intros e.
  rewrite (subset_eq_compat _ _ x1 x2 i1 i2); try reflexivity; apply e.
Defined.
