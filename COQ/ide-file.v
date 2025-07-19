Require Import Reals.
Require Import Psatz.
From stdpp Require Import tactics.

Open Scope R_scope.

Lemma simplify_ineq :
  forall (a beta : R),
    a ≠ 0 ->
    -8 * beta ^ 2 / (8 * a) = - beta ^ 2 / a.
Proof.
  intros a beta H.
  field.
  assumption.
Qed.



Lemma simplify_ineq_1 :
  forall (a b : R),
    a ≠ 0 ->
    ((-1 / 2) ^ 2 * b ^ 2 + (-1 / 2) * b ^ 2) / a = (-1 / 4 * b ^ 2 / a).
Proof.
  intros a b H.
  field.
  assumption.
Qed.


Lemma simplify_ineq_2 :
  forall (a b : R),
    a ≠ 0 ->
    ((-1 / 2) ^ 2 * b ^ 2 + (-1 / 2) * b ^ 2) / a = - (b ^ 2) / (4 * a).
Proof.
  intros a b H.
  field.
  assumption.
Qed.


Lemma simplify_ineq_3 :
  forall (a b : R),
    a ≠ 0 ->
    -2 * b ^ 2 / (8 * a) = - b ^ 2 / (4 * a).
Proof.
  intros a b H.
  field.
  assumption.
Qed.


Lemma simplify_ineq_4 :
  forall (a b : R),
    a ≠ 0 ->
    - b ^ 2 / (4 * a) <= - b ^ 2 / (4 * a).
Proof.
  intros a b H.
  apply Rle_refl.
Qed.


Lemma simplify_ineq_5 :
  forall (a b : R),
    a ≠ 0 ->
    -2 * b ^ 2 / (8 * a) <= -2 * b ^ 2 / (8 * a).
Proof.
  intros a b H.
  apply Rle_refl.
Qed.

Lemma pos_implies_nonzero :
  forall (a : R), 0 < a -> a <> 0.
Proof.
  intros a H.
  lra.
Qed.



Lemma simplify_quad_inequality :
  forall (a b c d beta : R),
    0 < a ->
    beta = -(1/2) * b ->
    d = beta / a ->
    a * d ^ 2 + b * d + c <= a * (- b / (2 * a)) ^ 2 + b * (- b / (2 * a)) + c.
Proof.
  intros a b c d beta Hpos Hb Hd.
  
  apply Rplus_le_compat_r with (r := c).
  
  rewrite Hd.
  rewrite Hb.
  field_simplify.
  assert (Hnz: a <> 0) by lra.
  
  
  simplify_eq.
  
  apply Rle_refl.


  apply (pos_implies_nonzero a Hpos ).
  apply (pos_implies_nonzero a Hpos ).
  
Qed.



