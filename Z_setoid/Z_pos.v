From Coq Require Import Arith.
Require Import logic.
Require Import integer.
Require Import ProofIrrelevance.

Local Coercion is_true : bool >-> Sortclass.

Definition Z_pos: Set := {n : nat | 0 <? n }.

Definition Z_pos__N (p: Z_pos): nat := proj1_sig p.
Definition Z_pos__Z (p: Z_pos): integer := (proj1_sig p, 0).

Definition Z_pos_plus : Z_pos -> Z_pos -> Z_pos.
  intros [x xpos%Nat.ltb_lt] [y ypos%Nat.ltb_lt].
  refine (exist  _ (x + y) _).
  now apply Nat.ltb_lt, Nat.add_pos_pos.
Defined.

Definition Z_pos_mult : Z_pos -> Z_pos -> Z_pos.
  intros [x xpos%Nat.ltb_lt] [y ypos%Nat.ltb_lt].
  refine (exist  _ (x * y) _).
  now apply Nat.ltb_lt, Nat.mul_pos_pos.
Defined.

Lemma Z_pos_mult_compat: forall p q: Z_pos, Z_pos__N (Z_pos_mult p q) = Z_pos__N p * Z_pos__N q.
Proof. now intros [x xpos] [y ypos]. Defined.

Definition ZP1: Z_pos.
  refine (exist  _ 1 _). easy.
Defined.

Lemma Z_pos__N_injective:
  forall t1 t2: Z_pos, proj1_sig t1 = proj1_sig t2 -> t1 = t2.
Proof.
  intros [x1 i1] [x2 i2]; simpl; intros e.
  rewrite (subset_eq_compat _ _ x1 x2 i1 i2); try reflexivity; apply e.
Defined.
