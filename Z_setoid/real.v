Require Import Coq.omega.Omega.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import logic.
Require Import natural.
Require Import integer.
Require Import Z_pos.
Require Import rational.

Delimit Scope real_scope with real.
Open Scope real_scope.

Definition real: Type := nat -> rational.

Notation "0" := (fun n => Q0).
Notation "1" := (fun n => Q1).

Definition R_tend_to_zero (a: real): Prop :=
forall (epsilon: rational), epsilon >Q Q0 ->
  exists (N: nat), forall (n: nat), n > N -> Q_abs (a n) <Q epsilon.

Example R_reciprocals_tend_to_zero: R_tend_to_zero (fun n => ((1, 0) // N__Z_pos n)).
Proof. unfold R_tend_to_zero. intros. 
Admitted.
