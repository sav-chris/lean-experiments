Require Import Reals.
Require Import Psatz.

Open Scope R_scope.


Lemma le_add_both_sides : forall a b c : R, a + c <= b + c -> a <= b.
Proof.
  intros a b c H.
  apply Rplus_le_reg_r with (r := c).
  exact H. 
Qed.


Lemma le_add_both_sides_explicit (a b c : R) :
  a + c <= b + c -> a <= b.
Proof.
  apply Rplus_le_reg_r.
Qed.


Lemma simplify_quad_inequality :
  forall (a b c d beta : R),
    0 < a ->
    b = -2 * beta ->
    d = beta / a ->
    a * d ^ 2 + b * d + c <= a * (- b / (2 * a)) ^ 2 + b * (- b / (2 * a)) + c.
Proof.
  intros a b c d beta Hpos Hb Hd.

  set (L := a * d ^ 2 + b * d).
  set (R := a * (- b / (2 * a)) ^ 2 + b * (- b / (2 * a))).

  apply (le_add_both_sides_explicit (L + c) (R + c) 0).
  unfold L, R.


Abort.

