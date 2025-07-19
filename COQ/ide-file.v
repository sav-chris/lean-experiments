Require Import Reals.
Require Import Psatz.
From stdpp Require Import tactics.

Open Scope R_scope.


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
  simplify_eq.
  apply Rle_refl.
  lra.
  lra.  
Qed.



Definition quadratic (a b c x : R) : R :=
  a * x ^ 2 + b * x + c.
  
Definition quadratic_vertex (a h k x : R) : R :=
  a * (x - h) ^ 2 + k.

Definition quadratic_minimizer_point (a b : R) : R :=
  - b / (2 * a).

Definition quadratic_minimum (a b c : R) : R :=
  quadratic a b c (quadratic_minimizer_point a b).


Lemma square_shift_expansion :
  forall (a b x : R),
    a <> 0 ->
    (x - (- b / (2 * a))) ^ 2 =
    x ^ 2 + (b / a) * x + (b ^ 2) / (4 * a ^ 2).
Proof.
  intros a b x Ha.
  field_simplify.
  ring.
  lra.
  lra.
Qed.


Lemma simplify_quadratic_division :
  forall (a b c x : R),
    a <> 0 ->
    a * x ^ 2 + b * x + c = (4 * a ^ 2 * x ^ 2 + 4 * a * x * b + 4 * a * c) / (4 * a).
Proof.
  intros a b c x Ha.
  field_simplify.
  field.
  apply Ha.
  apply Ha.
Qed.




Lemma quadratic_eq_vertex_form :
  forall (a b c x : R),
    a <> 0 ->
    quadratic a b c x =
    quadratic_vertex a (- b / (2 * a)) (c - b ^ 2 / (4 * a)) x.
Proof.
  intros a b c x Ha.
  unfold quadratic, quadratic_vertex.
  rewrite (square_shift_expansion a b x Ha).
  field_simplify.
  field.
  apply Ha.
  apply Ha.
Qed.


Lemma vertex_quadratic_minimizer :
  forall (a h k x : R),
    0 < a ->
    quadratic_vertex a h k x >= quadratic_vertex a h k h.
Proof.
  intros a h k x Ha.
  unfold quadratic_vertex.
  assert (Hsq : 0 <= (x - h)^2) by apply Rle_0_sqr.
  assert (Hprod : 0 <= a * (x - h)^2) by (apply Rmult_le_pos; lra).
  replace (a * (h - h)^2 + k) with (0 + k) by (rewrite Rminus_diag_eq; simpl; lra).
  apply Rplus_le_compat_r.
  exact Hprod.
Qed.






