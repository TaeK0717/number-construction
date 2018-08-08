From Coq Require Import Arith.
Require Import Coq.omega.Omega.
Require Import logic.
Require Import natural.
Require Import integer.
Require Import ProofIrrelevance.

Local Coercion is_true : bool >-> Sortclass.

Definition Z_nonzero: Set := {m : integer | ~ m =Z= Z0 }.

Definition Z_nonzero__Z (p: Z_nonzero): integer := proj1_sig p.

Definition Z_nonzero_mult : Z_nonzero -> Z_nonzero -> Z_nonzero.
  intros [x xnz] [y ynz].
  refine (exist  _ (x *Z y) _).
  unfold is_true in xnz, ynz.
  destruct x, y.
  unfold Z_eq in xnz, ynz.
  zero_in xnz; zero_in ynz.
  unfold Z_eq. simpl. zero.
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
forall p q: Z_nonzero, Z_nonzero__Z (Z_nonzero_mult p q) =Z= Z_nonzero__Z p *Z Z_nonzero__Z q.
Proof. now intros [x xnz] [y ynz]. Defined.

Definition ZN1: Z_nonzero.
  refine (exist  _ Z1 _). easy.
Defined.
