# Coq custom number construction
## Theorem Lists
### Natural Number

* ```Lemma N_eq_plus_cons: forall a b c: nat, a = b <-> c + a = c + b.```
* ```Lemma N_lt_plus_cons: forall a b c: nat, a < b <-> c + a < c + b.```
* ```Lemma N_trichotomy: forall a b: nat, a <> b -> minus a b <> 0 \/ minus b a <> 0.```
* ```Lemma N_S_inj: forall k l: nat, S k = S l -> k = l.```
* ```Lemma N_S_surj: forall k l: nat, k = l -> S k = S l.```
* ```Lemma N_minus_plus: forall n n0, n - n0 <> 0 -> (n - n0) + n0 = n.```
* ```Lemma N_plus_minus: forall x y: nat, x + y - y = x.```
* ```Lemma N_mult_n_Sm: forall a b: nat, a * S b = a + a * b.```
* ```Lemma N_mult_nonzero_inj: forall z x y: nat, S z * x = S z * y -> x = y.```
* ```Lemma N_le__eq_lt: forall n m: nat, n <= m <-> n = m \/ n < m.```
* ```Lemma N_not_le__gt: forall n m: nat, ~ n <= m <-> n > m.```
* ```Lemma N_le_lt__lt: forall a b c d: nat, a <= b /\ c < d -> a + c < b + d.```
* ```Lemma N_le_le__le: forall a b c d: nat, a <= b /\ c <= d -> a + c <= b + d.```
* ```Lemma N_lt_mult_nonzero: forall a b c: nat, a < b -> a * S c < b * S c.```
* ```Lemma N_rearr: forall a b c d: nat, a < b /\ c < d -> a * d + b * c < a * c + b * d.```

### Integer

* ```Theorem Z_refl: Reflexive Z_eq.```
* ```Theorem Z_symm: Symmetric Z_eq.```
* ```Theorem Z_tran: Transitive Z_eq.```
* ```Theorem Z_1: forall x y z: integer, (x + y) + z =Z= x + (y + z).```
* ```Theorem Z_2: forall x y: integer, x + y =Z= y + x.```
* ```Theorem Z_3: forall x: integer, x + 0 =Z= x.```
* ```Theorem Z_4: forall x: integer, x + - x =Z= 0.```
* ```Theorem Z_5: forall x y z: integer, (x * y) * z =Z= x * (y * z).```
* ```Theorem Z_6: forall x y: integer, x * y =Z= y * x.```
* ```Theorem Z_7: forall x: integer, x * 1 =Z= x.```
* ```Theorem Z_8: forall x y z: integer, x * (y + z) =Z= x * y + x * z.```
* ```Theorem Z_9: forall x y: integer, x * y =Z= 0 -> x =Z= 0 \/ y =Z= 0.```
* ```Lemma Z_neg_diff__lt: forall x y: integer, x - y <Z 0 <-> x <Z y.```
* ```Lemma Z_no_diff__eq: forall x y: integer, x - y =Z= 0 <-> x =Z= y.```
* ```Lemma Z_pos_diff__gt: forall x y: integer, x - y >Z 0 <-> x >Z y.```
* ```coq
  Lemma Z_10_0: forall x: integer,
    (  x <Z 0 /\ ~ x =Z= 0 /\ ~ x >Z 0) \/
    (~ x <Z 0 /\   x =Z= 0 /\ ~ x >Z 0) \/
    (~ x <Z 0 /\ ~ x =Z= 0 /\   x >Z 0).```
* ```coq
  Theorem Z_10: forall x y: integer,
    (  x <Z y /\ ~ x =Z= y /\ ~ x >Z y) \/
    (~ x <Z y /\   x =Z= y /\ ~ x >Z y) \/
    (~ x <Z y /\ ~ x =Z= y /\   x >Z y).```
* ```Theorem Z_11: forall x y z: integer, x <Z y /\ y <Z z -> x <Z z.```
* ```Theorem Z_12: forall x y z: integer, x <Z y -> x + z <Z y + z.```
* ```Theorem Z_13: forall x y z: integer, x <Z y /\ z >Z 0 -> x * z <Z y * z.```
* ```Theorem Z_14: 0 <Z> 1.```
* ```Lemma Z_not_not_equal: forall z w: integer, z =Z= w <-> ~ z <Z> w.```
* ```Lemma Z_mult_0: forall z: integer, z * 0 =Z= 0.```
* ```Lemma Z_mult_neg_1: forall z: integer, - z =Z= (0, 1) * z.```
* ```Lemma Z_le_inv: forall z w: integer, z <=Z w <-> - z >=Z - w.```
* ```Lemma Z_eq_mult_cons: forall a b c: integer, c <Z> 0 -> a =Z= b <-> c * a =Z= c * b.```
* ```Lemma Z_pos_int_nonzero: forall p: pos_int, make_pos_int p <Z> Z0.```

### Rational Number

* ```Theorem Q_refl: Reflexive Q_eq.```
* ```Theorem Q_symm: mmetric Q_eq.```
* ```Theorem Q_tran: Transitive Q_eq.```
