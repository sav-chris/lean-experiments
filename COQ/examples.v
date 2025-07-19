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


Lemma simplify_quad_inequality :
  forall (a b c d beta : R),
    0 < a ->
    b = -2 * beta ->
    d = beta / a ->
    a * d ^ 2 + b * d + c <= a * (- b / (2 * a)) ^ 2 + b * (- b / (2 * a)) + c.
Proof.
  intros a b c d beta Hpos Hb Hd.
  
  apply Rplus_le_compat_r with (r := c).
  
  rewrite Hd.
  rewrite Hb.
  field_simplify.
  assert (a <> 0) by lra.
  assert (Hineq : - beta ^ 2 / a <= - beta ^ 2 / a) by lra.
  (*assert (Hbeta : beta = -0.5 * b) by (rewrite Hb; lra). *)
  
  simplify_eq.
  
  rewrite (simplify_ineq a beta H).
  
  (*apply Rle_refl. *)
  
  (*rewrite <- Hbeta.*)

  
  Show.
Qed.

(***********************)

replace (((-0.5) ^ 2 * b ^ 2 + -0.5 * b ^ 2) / a) with (-0.25 * b ^ 2 / a) by field.
  replace (-2 * b ^ 2 / (8 * a)) with (-0.25 * b ^ 2 / a) by field.
  apply Rle_refl.


(************************************)

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



Lemma simplify_quad_inequality :
  forall (a b c d beta : R),
    0 < a ->
    (*b = -2 * beta ->*)
    beta = -(1/2) * b ->
    d = beta / a ->
    a * d ^ 2 + b * d + c <= a * (- b / (2 * a)) ^ 2 + b * (- b / (2 * a)) + c.
Proof.
  intros a b c d beta Hpos Hb Hd.
  
  apply Rplus_le_compat_r with (r := c).
  
  rewrite Hd.
  rewrite Hb.
  field_simplify.
  assert (a <> 0) by lra.
  (*assert (Hineq : - beta ^ 2 / a <= - beta ^ 2 / a) by lra.*)
  (*assert (Hbeta : beta = -0.5 * b) by (rewrite Hb; lra). *)
  
  simplify_eq.
  
  rewrite (simplify_ineq_3 a b H).
  
  Show.
  
  

  (*replace (-0.5) with (-1 / 2) by field.*)
  
(*  rewrite (simplify_ineq_2 a b H). *)
  (*rewrite (simplify_ineq_1 a b H). *)

  
  
  (*rewrite (simplify_ineq a beta H).*)
  
  (*apply Rle_refl. *)
  
  (*rewrite <- Hbeta.*)

  
  Show.
Qed.

(*************************************)


  (*replace (-0.5) with (-1 / 2) by field.*)
  
(*  rewrite (simplify_ineq_2 a b H). *)
  (*rewrite (simplify_ineq_1 a b H). *)

  
  
  (*rewrite (simplify_ineq a beta H).*)
  
  (*apply Rle_refl. *)
  
  (*rewrite <- Hbeta.*)

(*************************************)  

  rewrite (simplify_ineq_5 a b H).

  (*assert (Hineq : - beta ^ 2 / a <= - beta ^ 2 / a) by lra.*)
  (*assert (Hbeta : beta = -0.5 * b) by (rewrite Hb; lra). *)
  

(*********************)

(* main.coq *)

Require Import String.
Open Scope string_scope.

Require Import Reals.
Require Import Psatz.

Open Scope R_scope.


(* Define a simple string *)
Definition hello := "Hello, world!"%string.

(* A trivial theorem about the string *)
Theorem hello_is_not_empty : hello <> EmptyString.
Proof.
  unfold hello.
  discriminate.
Qed.


Lemma le_add_both_sides : forall a b c : R, a + c <= b + c -> a <= b.
Proof.
  intros a b c H.
  (* Subtract c from both sides *)
  apply Rplus_le_reg_r with (r := c).
  exact H. 
Qed.


Require Import Reals.
Open Scope R_scope.

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

  apply le_add_both_sides.
  unfold L, R.


Abort.

(*****************************)


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


Lemma quadratic_eq_vertex_form :
  forall (a b c x : R),
    a <> 0 ->
    quadratic a b c x =
    quadratic_vertex a (- b / (2 * a)) (c - b ^ 2 / (4 * a)) x.
Proof.
  intros a b c x Ha.
  unfold quadratic, quadratic_vertex.
  assert (H1 : (x - (- b / (2 * a))) ^ 2 =
               x ^ 2 + (b / a) * x + (b ^ 2) / (4 * a ^ 2)).
  {
    field_simplify [Ha].
    ring.
  }
  rewrite H1.
  field_simplify [Ha].
  ring.
Qed.


(*********************************)


Lemma simplify_ineq_1 :
  forall (a b : R),
    a ≠ 0 ->
    ((-1 / 2) ^ 2 * b ^ 2 + (-1 / 2) * b ^ 2) / a = (-1 / 4 * b ^ 2 / a).
Proof.
  intros a b H.
  field.
  assumption.
Qed.


Lemma simplify_ineq :
  forall (a beta : R),
    a ≠ 0 ->
    -8 * beta ^ 2 / (8 * a) = - beta ^ 2 / a.
Proof.
  intros a beta H.
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

(*********************************************)


