Require Import Coq.omega.Omega.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import logic.
Require Import natural.
Require Import integer.
Require Import Z_nonzero.
Require Import rational.

Delimit Scope real_scope with real.
Open Scope real_scope.

Notation "'SQ0'" := (fun n => Q0).
Notation "'SQ1'" := (fun n => Q1).

Definition Cauchy (a: nat -> rational): Prop :=
forall (epsilon: rational), epsilon >Q Q0 ->
  exists (N: nat), forall (n m: nat), n > N -> m > N -> Q_abs (a n -Q a m) <Q epsilon.

Definition real: Type := {r: nat -> rational | Cauchy r}.

Definition Bounded (a: nat -> rational): Prop :=
  exists (M: rational), M >Q Q0 /\ forall (n: nat), Q_abs (a n) <=Q M.

Theorem R_Cauchy__Bounded: forall a: nat -> rational, Cauchy a -> Bounded a.
Proof. intros a ca. unfold Cauchy in ca. unfold Bounded.
  destruct (ca Q1) as [N]. easy.
  exists (Q_max (Q_seq_max (fun n => Q_abs (a n)) N) (Q_abs (a (S N)) +Q Q1)).
  assert (forall p q: rational, Q_max p q >=Q q).
    intros. unfold Q_max. remember (Q_leb p q) as b; destruct b; symmetry in Heqb.
    easy. rewrite Q_leb_false__gt in Heqb. now apply Q_gt_ge_subrel.
  assert (forall p q: rational, Q_max p q >=Q p).
    intros. unfold Q_max. remember (Q_leb p q) as b; destruct b; symmetry in Heqb.
    rewrite Q_leb_true__le in Heqb. easy. easy.
  split. assert (Q1 >Q Q0) by easy.
  assert (forall p q r: rational, p >=Q q -> q >Q r -> p >Q r).
    intros. now rewrite <- H3.
  apply (H3 _ (Q_abs (a (S N)) +Q Q1)). apply H0.
  assert (Q_abs (a (S N)) >=Q Q0). rewrite <- Q_abs__nonneg. easy.
  rewrite <- H4. easy.
  intros. pose proof (N_trichotomy n N). destruct H2.
    rewrite <- H1. remember (fun n0 : nat => Q_abs (a n0)) as b.
    assert (Q_abs (a n) =Q= b n). rewrite Heqb. reflexivity. rewrite H3.
    apply Q_seq_max_ge. omega.
  destruct H2.
    rewrite <- H1. remember (fun n0 : nat => Q_abs (a n0)) as b.
    assert (Q_abs (a n) =Q= b n). rewrite Heqb. reflexivity. rewrite H3.
    apply Q_seq_max_ge. omega.

  rewrite <- H0.
  assert ((a n -Q a (S N)) +Q (a (S N)) =Q= a n).
    unfold Q_minus. rewrite Q_1. rewrite (Q_2 _ (a (S N))).
    assert (a (S N) -Q a (S N) =Q= Q0) by apply Q_4. unfold Q_minus in H3.
    rewrite H3. apply Q_3.
  rewrite <- H3. rewrite Q_triangle_ineq.
  rewrite Q_2.
  assert (Q_abs (a n -Q a (S N)) <Q Q1).
    apply H. apply H2. omega.
  assert (forall x y z: rational, y >Q z -> x +Q y >Q x +Q z).
    intros. repeat rewrite (Q_2 x). apply Q_12. apply H5.
  apply Q_gt_ge_subrel. apply H5. apply H. apply H2. omega.
Defined.

Definition R_eq_0 (a: nat -> rational): Prop :=
forall (epsilon: rational), epsilon >Q Q0 ->
  exists (N: nat), forall (n: nat), n > N -> Q_abs (a n) <Q epsilon.

Definition R_eq_0_real (a: real): Prop :=
forall (epsilon: rational), epsilon >Q Q0 ->
  exists (N: nat), forall (n: nat), n > N -> Q_abs (proj1_sig a n) <Q epsilon.

Lemma R_cons: forall a b: real, Cauchy (fun n => (proj1_sig a n -Q proj1_sig b n)).
  intros. destruct a as [a ca], b as [b cb]. unfold Cauchy. simpl.
  unfold Cauchy in ca, cb.
  intros epsilon Heps.
  pose proof (Q_cons_pos_div_QN2 epsilon Heps) as Heps2.
  pose proof (ca (epsilon /Q QN2) Heps2) as Ha; destruct Ha as [Na].
  pose proof (cb (epsilon /Q QN2) Heps2) as Hb; destruct Hb as [Nb].
  exists (max Na Nb). intros n m Hn' Hm'.
  pose proof (N_gt_max _ _ _ Hn') as Hn; destruct Hn as [Hna Hnb].
  pose proof (N_gt_max _ _ _ Hm') as Hm; destruct Hm as [Hma Hmb].
  clear Hn' Hm' Heps Heps2 ca cb.
  assert (Q_abs (a n -Q a m) +Q Q_abs (b n -Q b m) <Q epsilon).
    rewrite <- (Q_double_half epsilon).
    apply (Q_cons_lt_plus _ _ _ _ (H n m Hna Hma) (H0 n m Hnb Hmb)).
  assert (Q_abs (a n -Q b n -Q (a m -Q b m)) <=Q Q_abs (a n -Q a m) +Q Q_abs (b n -Q b m)).
    assert (a n -Q b n -Q (a m -Q b m) =Q= (a n -Q a m) -Q (b n -Q b m)).
      unfold Q_minus. rewrite Q_mult_neg_distr.
      assert (forall q: rational, -Q -Q q =Q= q). destruct q as [[q1 q2] [[q3 q4] q5]]; simpl.
        repeat rewrite (mult_comm q3), (mult_comm q4). omega.
      unfold Q_minus. rewrite H2. repeat rewrite <- Q_1.
      rewrite (Q_1 (a n)). rewrite (Q_2 (-Q b n)). rewrite Q_mult_neg_distr.
      unfold Q_minus. rewrite H2. repeat rewrite Q_1. reflexivity.
    rewrite H2. unfold Q_minus. rewrite <- (Q_cons_abs_neg (b n +Q -Q b m)).
    rewrite Q_triangle_ineq. easy.
  rewrite H2. apply H1.
Defined.

Definition R_eq (a b: real): Prop := R_eq_0 (fun n => (proj1_sig a n -Q proj1_sig b n)).

Notation "p =R= q" := (R_eq p q) (at level 70): type_scope.
Notation "p <R> q" := (~ p =R= q) (at level 70): type_scope.

Theorem R_refl: Reflexive R_eq.
Proof.
  (* reflexivity *) unfold Reflexive. intros.
  unfold R_eq, R_eq_0.
  intros. exists 0%nat. intros.
  assert (Q_abs (proj1_sig x n -Q proj1_sig x n) =Q= Q0). rewrite Q_4. reflexivity.
  rewrite H1. apply H.
Defined.

Theorem R_symm: Symmetric R_eq.
Proof.
  (* symmetricity *) unfold Symmetric.
  unfold R_eq, R_eq_0.
  intros. destruct x as [x Hx], y as [y Hy]; simpl. simpl in H.
  assert (forall n: nat, Q_abs (x n -Q y n) =Q= Q_abs (y n -Q x n)).
    intros.
    assert (x n -Q y n =Q= -Q (y n -Q x n)).
      rewrite <- Q_7_2. unfold Q_minus. rewrite Q_9_0.
      rewrite Q_7_2. rewrite (Q_2 (-Q y n)). rewrite Q_7_2.
      assert (forall p: rational, -Q -Q p =Q= p).
        destruct p, i. unfold Q_neg, Z_neg. reflexivity.
      rewrite H1. reflexivity.
    rewrite H1. rewrite Q_cons_abs_neg. reflexivity.
  pose proof (H epsilon H0). destruct H2. exists x0. intros. rewrite <- H1.
  apply H2. apply H3.
Defined.

Theorem R_tran: Transitive R_eq.
Proof.
  unfold Transitive.
  unfold R_eq, R_eq_0.
  intros x y z H H0 epsilon H1'.
  destruct x as [x cx], y as [y cy], z as [z cz]; simpl. simpl in H, H0, H1'.
  assert (epsilon /Q QN2 >Q Q0).
    destruct epsilon. unfold QN2. simpl. rewrite Z_nonzero_mult_compat. simpl.
    simpl in H1'. rewrite Z_7 in H1'. rewrite Z_7_0 in H1'.
    rewrite Z_7_0. repeat rewrite Z_7. apply H1'.

  pose proof (H (epsilon /Q QN2) H1) as Hx.
  pose proof (H0 (epsilon /Q QN2) H1) as Hy.
  destruct Hx as [Nx], Hy as [Ny].
  exists (max Nx Ny).
  assert (forall n a b: nat, n > Init.Nat.max a b -> n > a /\ n > b).
    induction n. intros. inversion H4.
    destruct a; destruct b; try (intros; simpl; omega); simpl; try omega.
    assert (forall p q: nat, S p > S q <-> p > q) by (intros; omega).
    repeat rewrite H4. apply IHn.
  intros. apply H4 in H5. destruct H5. apply H2 in H5. apply H3 in H6.

  assert (x n -Q z n =Q= (x n -Q y n) +Q (y n -Q z n)).
    unfold Q_minus. rewrite <- Q_1. rewrite (Q_1 (x n) (-Q y n)).
    rewrite (Q_2 _ (y n)). assert ((y n) -Q (y n) =Q= Q0) by apply Q_4.
    unfold Q_minus in H7. rewrite H7. rewrite Q_3. reflexivity.
  rewrite H7.
  assert ((epsilon /Q QN2) +Q (epsilon /Q QN2) =Q= epsilon).
    rewrite Q_double.
    assert (Q1 +Q Q1 =Q= proj1_sig QN2) by reflexivity.
    rewrite H8; clear H8. rewrite Q_5.
    assert (proj1_sig (/Q QN2) *Q proj1_sig QN2 =Q= Q1) by apply Q_8_0.
    rewrite H8; clear H8. apply Q_7.
  assert (epsilon >Q Q_abs (x n -Q y n) +Q Q_abs (y n -Q z n))
    by (rewrite <- H8; apply (Q_cons_lt_plus _ _ _ _ H5 H6)).
  rewrite Q_triangle_ineq. apply H9.
Defined.

Add Parametric Relation:
  real R_eq
  reflexivity proved by R_refl
  symmetry proved by R_symm
  transitivity proved by R_tran
  as R.

Definition R_plus (a b: real): real.
  exists (fun n => (proj1_sig a n +Q proj1_sig b n)).
  destruct a as [a ca], b as [b cb].
  unfold Cauchy; simpl.
  unfold Cauchy in ca, cb.
  intros epsilon Heps.
  pose proof (Q_cons_pos_div_QN2 epsilon Heps) as Heps2.
  pose proof (ca (epsilon /Q QN2) Heps2) as Ha; destruct Ha as [Na].
  pose proof (cb (epsilon /Q QN2) Heps2) as Hb; destruct Hb as [Nb].
  exists (max Na Nb). intros n m Hn' Hm'.
  pose proof (N_gt_max _ _ _ Hn') as Hn; destruct Hn as [Hna Hnb].
  pose proof (N_gt_max _ _ _ Hm') as Hm; destruct Hm as [Hma Hmb].
  clear Hn' Hm' Heps Heps2 ca cb.
  assert (Q_abs (a n -Q a m) +Q Q_abs (b n -Q b m) <Q epsilon).
    rewrite <- (Q_double_half epsilon).
    apply (Q_cons_lt_plus _ _ _ _ (H n m Hna Hma) (H0 n m Hnb Hmb)).
  assert (Q_abs (a n +Q b n -Q (a m +Q b m)) <=Q Q_abs (a n -Q a m) +Q Q_abs (b n -Q b m)).
    unfold Q_minus. rewrite Q_mult_neg_distr. rewrite Q_1. unfold Q_minus. rewrite <- (Q_1 (b n)).
    rewrite (Q_2 (b n)). rewrite Q_1. rewrite <- Q_1. rewrite Q_triangle_ineq. easy.
  rewrite H2. apply H1.
Defined.

Add Morphism R_plus with signature R_eq ==> R_eq ==> R_eq as R_plus_morph.
Proof. (* well-definedness of R_plus *)
  intros. unfold R_plus, R_eq, R_eq_0. unfold R_eq, R_eq_0 in H, H0. simpl.
  destruct x as [x cx], y as [y cy], x0 as [x0 cx0], y0 as [y0 cy0].
  simpl. simpl in H, H0.

  intros epsilon H1'.
  assert (epsilon /Q QN2 >Q Q0).
    destruct epsilon. unfold QN2. simpl. rewrite Z_nonzero_mult_compat. simpl.
    simpl in H1'. rewrite Z_7 in H1'. rewrite Z_7_0 in H1'.
    rewrite Z_7_0. repeat rewrite Z_7. apply H1'.

  pose proof (H (epsilon /Q QN2) H1) as Hx.
  pose proof (H0 (epsilon /Q QN2) H1) as Hy.
  destruct Hx as [Nx], Hy as [Ny].
  exists (max Nx Ny).
  assert (forall n a b: nat, n > Init.Nat.max a b -> n > a /\ n > b).
    induction n. intros. inversion H4.
    destruct a; destruct b; try (intros; simpl; omega); simpl; try omega.
    assert (forall p q: nat, S p > S q <-> p > q) by (intros; omega).
    repeat rewrite H4. apply IHn.
  intros. apply H4 in H5. destruct H5. apply H2 in H5. apply H3 in H6.

  assert (x n +Q x0 n -Q (y n +Q y0 n) =Q= (x n -Q y n) +Q (x0 n -Q y0 n)).
    unfold Q_minus. rewrite Q_1. rewrite Q_mult_neg_distr. unfold Q_minus.
    rewrite <- (Q_1 (x0 n)). rewrite (Q_2 (x0 n)). repeat rewrite <- Q_1.
    reflexivity.
  rewrite H7.

  assert ((epsilon /Q QN2) +Q (epsilon /Q QN2) =Q= epsilon).
    rewrite Q_double.
    assert (Q1 +Q Q1 =Q= proj1_sig QN2) by reflexivity.
    rewrite H8; clear H8. rewrite Q_5.
    assert (proj1_sig (/Q QN2) *Q proj1_sig QN2 =Q= Q1) by apply Q_8_0.
    rewrite H8; clear H8. apply Q_7.

  assert (epsilon >Q Q_abs (x n -Q y n) +Q Q_abs ((x0 n -Q y0 n)))
    by (rewrite <- H8; apply (Q_cons_lt_plus _ _ _ _ H5 H6)).
  rewrite Q_triangle_ineq. apply H9.
Defined.

Notation "p '+' q" := (R_plus p q) (at level 50, left associativity) : real_scope.
Notation "p '+R' q" := (R_plus p q) (at level 50, left associativity) : type_scope.

(** negation of a real number: q |-> -q *)
Definition R_neg (a: real): real.
  exists (fun n => -Q proj1_sig a n).
  destruct a as [a ca].
  unfold Cauchy; simpl.
  unfold Cauchy in ca.
  intros epsilon Heps.
  pose proof (ca epsilon Heps) as Ha; destruct Ha as [Na].
  exists Na. intros n m Hn Hm.
  clear Heps ca. rewrite <- Q_mult_neg_distr.
  rewrite Q_cons_abs_neg. apply (H n m Hn Hm).
Defined.

Add Morphism R_neg with signature R_eq ==> R_eq as R_neg_morph.
Proof. (* well-definedness of R_neg *)
  intros. unfold R_neg, R_eq, R_eq_0. unfold R_eq, R_eq_0 in H. simpl.
  destruct x as [x cx], y as [y cy].
  simpl. simpl in H. intros epsilon Heqs.
  destruct (H epsilon Heqs) as [N]. exists N. intros.
  rewrite <- Q_mult_neg_distr. rewrite Q_cons_abs_neg. apply (H0 n H1).
Defined.

Notation "'-' q" := (R_neg q) (at level 35, right associativity) : real_scope.
Notation "'-R' q" := (R_neg q) (at level 35, right associativity) : type_scope.

(** subtraction *)

Definition R_minus (a b: real) := a + -b.

Add Morphism R_minus with signature R_eq ==> R_eq ==> R_eq as R_minus_morph.
Proof. (* well-definedness of Z_minus *)
  unfold R_minus. intros. now rewrite H, H0.
Defined.

Notation "p '-' q" := (R_minus p q) (at level 50, left associativity) : real_scope.
Notation "p '-R' q" := (R_minus p q) (at level 50, left associativity) : type_scope.

(** multiplication *)
Definition R_mult (a b: real): real.
  exists (fun n => proj1_sig a n *Q proj1_sig b n).
  destruct a as [a ca'], b as [b cb'].
  pose proof (R_Cauchy__Bounded a ca') as ba.
  pose proof (R_Cauchy__Bounded b cb') as bb.
  unfold Cauchy; simpl.
  unfold Cauchy in ca', cb'.
  intros epsilon Heps.

  unfold Bounded in ba, bb.
  destruct ba as [MA1 [ba1 ba2]], bb as [MB1 [bb1 bb2]].
  assert (MAN: MA1 <Q> Q0). rewrite Q_10_2. left. apply ba1. rewrite Q_nonzero__iff in MAN.
  assert (MBN: MB1 <Q> Q0). rewrite Q_10_2. left. apply bb1. rewrite Q_nonzero__iff in MBN.
  remember (exist (fun q: rational => Q_numerator q <Z> Z0) MA1 MAN) as MA.
  remember (exist (fun q: rational => Q_numerator q <Z> Z0) MB1 MBN) as MB.
  assert (Hepsa: epsilon /Q Q_nonzero_mult QN2 MA >Q Q0). admit.
  assert (Hepsb: epsilon /Q Q_nonzero_mult QN2 MB >Q Q0). admit.

  pose proof (ca' (epsilon /Q (Q_nonzero_mult QN2 MA)) Hepsa).
  pose proof (cb' (epsilon /Q (Q_nonzero_mult QN2 MB)) Hepsb).
  destruct H as [Na Ha]. destruct H0 as [Nb Hb].
  exists (max Na Nb). intros.

  assert (a n *Q b n -Q a m *Q b m =Q= (a n *Q b n -Q a n *Q b m) +Q (a n *Q b m -Q a m *Q b m)).
    unfold Q_minus. repeat rewrite Q_1. rewrite <- (Q_1 _ (a n *Q b m)), (Q_2 _ (a n *Q b m)).
    assert (forall q: rational, q -Q q =Q= Q0) by apply Q_4. unfold Q_minus in H1. rewrite H1.
    rewrite (Q_2 Q0). rewrite Q_3. reflexivity.
  rewrite H1.
  rewrite Q_triangle_ineq.

  (* TODO: complete the proof. *)
Admitted.

Add Morphism R_mult with signature R_eq ==> R_eq ==> R_eq as R_mult_morph.
Proof. Admitted.
Notation "p '*' q" := (R_mult p q) (at level 40, left associativity) : real_scope.
Notation "p '*R' q" := (R_mult p q) (at level 40, left associativity) : type_scope.

Definition R_nonzero: Type := {q : real | ~ R_eq_0 (proj1_sig q)}.

(** reciprocal of a real number: q |-> -q *)
Definition R_recip (q: R_nonzero): R_nonzero.
Admitted.

Definition R_nonzero_eq (p q: R_nonzero): Prop := (proj1_sig p) =R= (proj1_sig q).

Add Morphism R_recip with signature R_nonzero_eq ==> R_nonzero_eq as R_recip_morph.
Proof. (* well-definedness of R_recip *)
Admitted.

Theorem R_nonzero_refl: Reflexive R_nonzero_eq.
Proof.
  (* reflexivity *) unfold Reflexive.
Admitted.

Theorem R_nonzero_symm: Symmetric R_nonzero_eq.
Proof.
  (* symmetricity *) unfold Symmetric.
Admitted.

Theorem R_nonzero_tran: Transitive R_nonzero_eq.
Proof.
  unfold Transitive.
Admitted.

Add Parametric Relation:
  R_nonzero R_nonzero_eq
  reflexivity proved by R_nonzero_refl
  symmetry proved by R_nonzero_symm
  transitivity proved by R_nonzero_tran
  as R_nz.

Definition R_nonzero_mult (p q: R_nonzero): R_nonzero.
  exists ((proj1_sig p) * (proj1_sig q)).
Admitted.

Lemma R_nonzero__R_injective:
  forall p q: R_nonzero, proj1_sig p =R= proj1_sig q -> R_nonzero_eq p q.
Proof.
  intros [x1 i1] [x2 i2]; simpl; intros e. unfold Q_nonzero_eq. simpl. apply e.
Defined.

Definition R_nonzero_1: R_nonzero.
Admitted.

Notation "'/' q" := (R_recip q) (at level 35, right associativity) : real_scope.
Notation "'/R' q" := (R_recip q) (at level 35, right associativity) : type_scope.

Theorem R_1: forall p q r: real, p + q + r =R= p + (q + r).
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




(** NOT YET MODIFIED **)





Theorem Q_2: forall p q: real, p + q =Q= q + p.
Proof. intros. destruct p, q. unfold Q_plus. unfold Q_eq.
  unfold Z_pos__Z. rewrite Z_pos_mult_compat. rewrite Z_8, Z_8_0. unfold Z_pos__Z. rewrite Z_pos_mult_compat.
  rewrite (Z_6 (i *Z (proj1_sig z0, 0))), (Z_6 (i0 *Z (proj1_sig z, 0))).
  rewrite (mult_comm (Z_pos__N z0)).
  apply Z_2.
Defined.

Theorem Q_3: forall q: real, q + 0 =Q= q.
Proof. intros. destruct q. unfold Q_plus. unfold Q_eq. rewrite Z_3. rewrite (Z_6 _ i).
  unfold Z_pos__Z. rewrite Z_5. rewrite Z_pos_mult_compat. simpl. zero.
  assert (forall a: nat, (a * 1)%nat = a) by (intros; omega). rewrite H. reflexivity.
Defined.

Theorem Q_4: forall q: real, q + -q =Q= 0.
Proof. intros. destruct q. unfold Q_neg, Q_plus, Q_eq.
  assert (forall a b: integer, -Z a *Z b =Z= -Z (a *Z b)).
  { destruct a, b. simpl. omega. }
  rewrite H. rewrite Z_4. simpl. zero.
Defined.

Theorem Q_5: forall p q r: real, p * q * r =Q= p * (q * r).
Proof. intros. destruct p, q, r. unfold Q_mult, Q_eq, Z_pos__Z.
  repeat rewrite Z_pos_mult_compat. rewrite (Z_5 i i0 i1). rewrite Z_6. rewrite <- mult_assoc. reflexivity.
Defined.

Theorem Q_6: forall p q: real, p * q =Q= q * p.
Proof. intros. destruct p, q. unfold Q_mult, Q_eq, Z_pos__Z. repeat rewrite Z_pos_mult_compat.
  rewrite Z_6. rewrite (Z_6 i i0). rewrite mult_comm. reflexivity.
Defined.

Theorem Q_7: forall q: real, q * 1 =Q= q.
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

Theorem Q_9: forall p q r: real, p * (q + r) =Q= p * q + p * r.
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
Definition Q_le (p q: real) := (** p <= q iff *)
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

Lemma Q_le_iff_neg: forall x: real, x <=Q 0 <-> Q_numerator x <=Z Z0.
Proof. destruct x.
  unfold Q_le. simpl. rewrite Z_7. reflexivity.
Defined.

Lemma Q_le_iff_pos: forall x: real, x >=Q 0 <-> Q_numerator x >=Z Z0.
Proof. destruct x.
  unfold Q_le. unfold Z_pos__Z.
  assert (proj1_sig ZP1 = 1%nat) by reflexivity. rewrite H.
  assert (Z0 *Z (proj1_sig z, 0) =Z= Z0) by reflexivity. rewrite H0.
  assert (Q_numerator (i // z) =Z= i) by reflexivity. rewrite H1.
  rewrite Z_7. reflexivity.
Defined.

Lemma Q_eq_iff: forall x: real, x =Q= 0 <-> Q_numerator x =Z= Z0.
Proof. destruct x.
  unfold Q_eq. unfold Z_pos__Z.
  assert (proj1_sig ZP1 = 1%nat) by reflexivity. rewrite H.
  assert ((proj1_sig z, 0) *Z Z0 =Z= Z0) by reflexivity. rewrite H0.
  assert (Q_numerator (i // z) =Z= i) by reflexivity. rewrite H1.
  rewrite Z_7. reflexivity.
Defined.

Lemma Q_neg_diff__lt: forall x y: real, x - y <Q 0 <-> x <Q y.
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
Lemma Q_no_diff__eq: forall x y: real, x - y =Q= 0 <-> x =Q= y.
Proof. intros. destruct x, y. unfold Q_le, Z_pos__Z, Q_minus, Q_neg, Q_plus, Q_eq.
  assert (forall t: integer, t *Z Z0 =Z= Z0). destruct t. zero.
  assert (forall a b: integer, -Z a *Z b =Z= -Z (a *Z b)).
         destruct a, b. unfold Z_neg, Z_mult, Z_eq. omega.
  rewrite Z_7. rewrite H, H0. rewrite Z_no_diff__eq. rewrite (Z_6 _ i0).
  easy.
Defined.
Lemma Q_pos_diff__gt: forall x y: real, x - y >Q 0 <-> x >Q y.
Proof. intros. destruct x, y.
  assert (forall t: integer, Z0 *Z t =Z= Z0). destruct t. zero.
  assert (forall a b: integer, -Z a *Z b =Z= -Z (a *Z b)).
         destruct a, b. unfold Z_neg, Z_mult, Z_eq. omega.
  unfold Q_le, Z_pos__Z, Q_minus, Q_neg, Q_plus.
  repeat rewrite H. rewrite Z_8_0.
  repeat rewrite H1. rewrite H0, H0. rewrite Z_pos_diff__gt.
  repeat rewrite Z_5. simpl. zero. one. easy.
Defined.
Lemma Q_10_0: forall x: real,
    (  x <Q 0 /\ ~ x =Q= 0 /\ ~ x >Q 0) \/
    (~ x <Q 0 /\   x =Q= 0 /\ ~ x >Q 0) \/
    (~ x <Q 0 /\ ~ x =Q= 0 /\   x >Q 0).
Proof.
  intros [ix rx]. repeat rewrite Q_le_iff_neg; repeat rewrite Q_le_iff_pos; repeat rewrite Q_eq_iff.
  assert (Q_numerator (ix // rx) =Z= ix) by reflexivity. rewrite H.
  apply Z_10.
Defined.

(** trichotomy *)
Theorem Q_10: forall x y: real,
  (  x <Q y /\ ~ x =Q= y /\ ~ x >Q y) \/
  (~ x <Q y /\   x =Q= y /\ ~ x >Q y) \/
  (~ x <Q y /\ ~ x =Q= y /\   x >Q y).
Proof.
  intros. rewrite <- Q_neg_diff__lt. rewrite <- Q_no_diff__eq. rewrite <- (Q_pos_diff__gt x y).
  apply Q_10_0.
Defined.

(** trichotomy *)
Corollary Q_10_1: forall x y: real, x <Q y \/ x =Q= y \/ x >Q y.
Proof.
  intros.
  pose proof (Q_10 x y).
  destruct H; destruct H.
  - left. apply H.
  - destruct H. destruct H0. right. left. apply H0.
  - destruct H. destruct H0. right. right. apply H1.
Defined.

(** transitivity *)
Theorem Q_11: forall x y z: real, x <Q y -> y <Q z -> x <Q z.
Proof. intros x y z. rewrite <- (Q_neg_diff__lt x y). rewrite <- (Q_neg_diff__lt x z). rewrite <- (Q_neg_diff__lt y z).
  assert (forall a b: real, a <Q 0 -> b <Q 0 -> a + b <Q 0).
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
    assert (forall q: real, 0 + q =Q= q).
    destruct q as [q q']. unfold Q_plus.
    assert (forall z: integer, Z0 +Z z =Z= z).
    destruct z2. simpl. omega.
    unfold Q_eq. rewrite H1. rewrite Z_7. unfold Z_pos__Z. rewrite Z_pos_mult_compat.
    rewrite Z_6. assert ((Z_pos__N ZP1 * Z_pos__N q')%nat = proj1_sig q') by zero.
    rewrite H2. reflexivity.
    rewrite H1. reflexivity. }
  intros. rewrite <- H0. apply (H (x - y) (y - z)). apply H1. apply H2. Defined.

(** addition preserves the order *)
Theorem Q_12: forall x y z: real, x <Q y -> x + z <Q y + z.
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

Theorem Q_13: forall p q r: real, p <Q q -> r >Q 0 -> p * r <Q q * r.
Proof. intros p q r H H'. destruct p as [np dp], q as [nq dq], r as [nr dr].
  simpl. unfold Z_pos__Z. repeat rewrite Z_pos_mult_compat.
  assert (forall a b: nat, (a * b, 0) =Z= (a, 0) *Z (b, 0)) by (intros; simpl; omega).
  repeat rewrite H0. repeat rewrite Z_5. repeat rewrite (Z_6 nr).
  repeat rewrite (Z_5 _ _ nr). rewrite <- (Z_5 nq), <- (Z_5 np).
  apply Z_13.
  simpl in H. unfold Z_pos__Z in H. apply H.
  simpl in H'. unfold Z_pos__Z in H'. simpl in H'. rewrite Z_7 in H'.
  assert (Z0 =Z= Z0 *Z nr) by (destruct nr; simpl; omega).
  rewrite H1. apply Z_13. simpl. destruct dr. simpl. unfold is_true in i.
  rewrite N_ltb_true__lt in i. omega. apply H'.
Defined.

Theorem Q_14: 0 <Q> 1.
Proof. simpl. easy. Defined.

Theorem Q_15: forall q: real, - q =Q= (-Z Q_numerator q // Q_denominator q). 
Proof. intros. destruct q. simpl. destruct i. simpl. zero. simpl. 
  rewrite plus_comm. rewrite (mult_comm _ n), (mult_comm _ n0). reflexivity.
Defined.
