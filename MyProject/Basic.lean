import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith


import Mathlib.Data.Finset.Basic

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Linear
--import Mathlib.Analysis.Calculus.Differentiable

import Mathlib.Analysis.Calculus.Deriv.Add


open scoped BigOperators
open Set Real Filter Topology


open Classical
open scoped NNReal ENNReal

def linear (m b x : ℝ) : ℝ := m * x + b

theorem linear_monotone {m b : ℝ} (h : 0 < m) :
    Monotone (linear m b) := by
    intros x y hxy

    simp only [linear]
    calc m * x + b ≤ m * y + b :=
      add_le_add_right (mul_le_mul_of_nonneg_left hxy (le_of_lt h)) b


theorem linear_monotone_decrease (m b : ℝ) (h : 0 > m) :
    Antitone (linear m b) := by
    intros x y hxy

    simp only [linear]
    calc  m * y + b ≤ m * x + b := by
    {
      apply add_le_add_right
      apply mul_le_mul_of_nonpos_left hxy (le_of_lt h)
    }


def quadratic_vertex (a h k x : ℝ) : ℝ := a * (x - h) ^ 2 + k

theorem vertex_quadratic_has_minimum (a h k : ℝ) (ha : 0 < a) :
    ∃ x₀, ∀ x, quadratic_vertex a h k x ≥ quadratic_vertex a h k x₀ := by
  use h
  intro x
  unfold quadratic_vertex
  have h1 : 0 ≤ (x - h) ^ 2 := sq_nonneg (x - h)
  have h2 : 0 ≤ a * (x - h) ^ 2 := mul_nonneg (le_of_lt ha) h1
  calc
    a * (x - h) ^ 2 + k ≥ 0 + k := add_le_add_right h2 k
    _ = a * (h - h) ^ 2 + k := by simp_all only
    [
      mul_nonneg_iff_of_pos_left,
      zero_add,
      sub_self,
      ne_eq,
      OfNat.ofNat_ne_zero,
      not_false_eq_true,
      zero_pow,
      mul_zero
    ]



def quadratic (a b c x : ℝ) : ℝ := a * (x ^ 2) + b * x + c

lemma quadratic_eq_vertex_form (a b c : ℝ) (ha : a ≠ 0) :
    ∀ x, quadratic a b c x = quadratic_vertex a (-b / (2 * a)) (c - b ^ 2 / (4 * a)) x := by
  intro x
  unfold quadratic quadratic_vertex
  have h1 : (x - (-b / (2 * a))) ^ 2 = x ^ 2 + (b / a) * x + (b ^ 2) / (4 * a ^ 2) := by
    field_simp [ha]
    ring
  rw [h1]
  field_simp [ha]
  ring


theorem quadratic_has_minimum (a b c : ℝ) (ha : 0 < a) :
    ∃ x₀, ∀ x, quadratic a b c x ≥ quadratic a b c x₀ := by
  let h := -b / (2 * a)
  let k := c - b ^ 2 / (4 * a)
  obtain ⟨x₀, hx₀⟩ := vertex_quadratic_has_minimum a h k ha
  have h_eq : ∀ x, quadratic a b c x = quadratic_vertex a h k x :=
    quadratic_eq_vertex_form a b c (ne_of_gt ha)
  use x₀
  intro x
  rw [h_eq x, h_eq x₀]
  exact hx₀ x


theorem vertex_quadratic_minimizer (a h k : ℝ) (ha : 0 < a) :
  ∀ x, quadratic_vertex a h k x ≥ quadratic_vertex a h k h := by
  intro x
  have h1 : 0 ≤ (x - h)^2 := sq_nonneg _
  have h2 : 0 ≤ a * (x - h)^2 := mul_nonneg (le_of_lt ha) h1
  calc
    a * (x - h)^2 + k ≥ 0 + k := add_le_add_right h2 k
    _ = a * (h - h)^2 + k := by simp

noncomputable def quadratic_minimizer_point (a b : ℝ) : ℝ := -b / (2 * a)

noncomputable def quadratic_minimum (a b c : ℝ) : ℝ :=
  quadratic a b c (quadratic_minimizer_point a b)


theorem quadratic_minimizer (a b c : ℝ) (ha : 0 < a) :
  ∀ p : ℝ, quadratic a b c p ≥ quadratic_minimum a b c := by
  let h := -b / (2 * a)
  let k := c - b^2 / (4 * a)
  have h_eq : ∀ p, quadratic a b c p = quadratic_vertex a h k p :=
    quadratic_eq_vertex_form a b c (ne_of_gt ha)
  have h_min := vertex_quadratic_minimizer a h k ha
  intro p
  unfold quadratic_minimum
  unfold quadratic_minimizer_point
  rw [h_eq p, h_eq h]
  exact h_min p

/-
theorem quadratic_minimizer (a b c : ℝ) (ha : 0 < a) :
    ∀ p : ℝ, quadratic a b c p ≥ quadratic a b c (-b / (2 * a)) := by
  let h := -b / (2 * a)
  let k := c - b^2 / (4 * a)
  have h_eq : ∀ p, quadratic a b c p = quadratic_vertex a h k p :=
    quadratic_eq_vertex_form a b c (ne_of_gt ha)
  have h_min := vertex_quadratic_minimizer a h k ha
  intro p
  rw [h_eq p, h_eq h]
  exact h_min p
-/




abbrev Pixel := ℕ × ℕ
abbrev Gradient := Pixel → ℝ × ℝ

def gradDot (f g : Gradient) (D : Finset Pixel) : ℝ :=
  ∑ x ∈ D,
    let (fx₁, fx₂) := f x
    let (gx₁, gx₂) := g x
    fx₁ * gx₁ + fx₂ * gx₂



def R (dI dB : Gradient) (D : Finset Pixel) (p : ℝ) : ℝ :=
  gradDot dI dI D - 2 * p * gradDot dB dI D + p ^ 2 * gradDot dB dB D

/-
def R (dI dB : Gradient) (D : Finset Pixel) (p : ℝ) : ℝ :=
  quadratic (gradDot (dB dB D), - 2 * gradDot (dB dI D), gradDot (dI dI D), p)
  --gradDot dI dI D - 2 * p * gradDot dB dI D + p ^ 2 * gradDot dB dB D
  --let c := gradDot dI dI D
  --let b := - 2 * gradDot dB dI D
  --let a := gradDot dB dB D
-/


noncomputable def p_opt (dI dB : Gradient) (D : Finset Pixel) : ℝ :=
  gradDot dI dB D / gradDot dB dB D



example (x : ℝ) :
    deriv (fun x ↦ x^2 ) x = 2 * x :=
  by
    simp


example (x : ℝ) :
    deriv (fun x ↦ 3 * x^2) x = 6 * x :=
  by
    simp only
    [
      differentiableAt_const,
      differentiableAt_fun_id,
      DifferentiableAt.fun_pow,
      deriv_fun_mul,
      deriv_const',
      zero_mul,
      deriv_fun_pow'',
      Nat.cast_ofNat,
      Nat.add_one_sub_one,
      pow_one,
      deriv_id'',
      mul_one,
      zero_add
    ]
    ring



lemma diff_pow_two (x : ℝ) : DifferentiableAt ℝ (fun y ↦ y ^ 2) x := by
  apply differentiableAt_fun_id.pow


lemma diff_pow_two_result (x : ℝ) : deriv ( fun y ↦ y ^ 2) x = 2 * x := by
  rw [deriv_pow 2]
  ring


lemma diff_pow_two_const (x : ℝ) : deriv ( fun y ↦ 3 * y ^ 2) x = 6 * x := by
  rw [deriv_const_mul 3 (diff_pow_two x)]
  rw [deriv_pow 2]
  ring



def f(x: ℝ) := 3 * x ^ 2
def g(x: ℝ) := 2 * x

lemma f_differentiable_at (x : ℝ) : DifferentiableAt ℝ f x :=
by
  apply DifferentiableAt.const_mul
  apply differentiableAt_fun_id.pow

lemma g_differentiable_at (x : ℝ) : DifferentiableAt ℝ g x :=
by
  apply DifferentiableAt.const_mul
  apply differentiableAt_id



lemma h2 (x : ℝ) : DifferentiableAt ℝ (g) x := by
    apply DifferentiableAt.const_mul
    exact differentiableAt_id



lemma poly_diff_example (x : ℝ) : deriv (f + g) x = 6 * x + 2 := by
  have h1 : DifferentiableAt ℝ f x := by
    apply DifferentiableAt.const_mul
    exact DifferentiableAt.pow differentiableAt_id 2
  have h2 : DifferentiableAt ℝ g x := by
    apply DifferentiableAt.const_mul
    exact differentiableAt_id
  rw [deriv_add h1 h2]
  unfold f g
  ring
  simp only
  [
    differentiableAt_fun_id, DifferentiableAt.fun_pow, differentiableAt_const,
    deriv_fun_mul, deriv_fun_pow'', Nat.cast_ofNat, Nat.reduceSub, pow_one,
    deriv_id'', mul_one, deriv_const', mul_zero, add_zero, one_mul
  ]
  ring

theorem test_a_b (a b c: ℝ)( hb: a >= b )(hc : b >= c) : a >= c := by
  exact ge_trans hb hc


lemma symmetry_grad (dI dB : Gradient)(D : Finset Pixel) : gradDot dI dB D = gradDot dB dI D := by
  unfold gradDot
  apply Finset.sum_congr rfl
  intro x hx
  simp only
  rw [mul_comm (dI x).1 (dB x).1, mul_comm (dI x).2 (dB x).2]


lemma simplify_quad_inequality
    (a b c d beta : ℝ)
    (h_pos : 0 < a)
    (h_beta : beta = - (1/2) * b)
    (h_d : d = beta / a) :
    a * d^2 + b * d + c ≤ a * (- b / (2 * a))^2 + b * (- b / (2 * a)) + c := by
  apply le_add_right
  rw [h_d, h_beta]
  field_simp [ne_of_gt h_pos]
  trace_state
  linarith


theorem R_has_minimum_at_p_opt
  (dI dB : Gradient) (D : Finset Pixel)
  (h : 0 < gradDot dB dB D) :
  ∀ p : ℝ, R dI dB D p ≥ R dI dB D (p_opt dI dB D) := by
    let a := gradDot dB dB D
    let beta := gradDot dB dI D
    let b := -2 * beta
    let c := gradDot dI dI D
    let d := p_opt dI dB D
    have ha    : a = gradDot dB dB D := rfl
    have hbeta : beta = gradDot dB dI D := rfl
    have hb    : b = -2 * beta := rfl
    have hc    : c = gradDot dI dI D := rfl
    have hd    : d = p_opt dI dB D := rfl
    have hz : 0 < a := h

    have R_eq (p : ℝ) : R dI dB D p = c - 2 * p * beta + p ^ 2 * a := by
      unfold R
      rw [←ha, ←hbeta, ←hc]


    have rhs_eq_quad (p : ℝ) : c - 2 * p * beta + p ^ 2 * a = quadratic a b c p := by
      rw [hb]
      unfold quadratic
      ring

    rw [R_eq]

    unfold R

    rw [rhs_eq_quad]

    have lhs_eq_quad (p : ℝ) :
      gradDot dI dI D - 2 * p * gradDot dB dI D + p ^ 2 * gradDot dB dB D =
      quadratic a b c p :=
      by
        rw [←hc, ←hbeta, ←ha, hb]
        unfold quadratic
        ring

    intro p
    rw [lhs_eq_quad]

    rw[←hd]

    have h_quad_ineq : quadratic a b c d ≥ quadratic_minimum a b c :=
      quadratic_minimizer a b c hz d

    apply ge_trans
    apply quadratic_minimizer a b c hz p

    unfold quadratic_minimum quadratic_minimizer_point quadratic

    -- TO DO: Refactor this into another lemma

    let lhs_1 := a * d ^ 2 + b * d
    have h_add_ineq_1 : a * d ^ 2 + b * d + c = lhs_1 + c := rfl

    let lhs_2 := a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a))
    have h_add_ineq_2 : a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c = lhs_2 + c := rfl

    rw [h_add_ineq_1, h_add_ineq_2] at *

    have lhs_leeq_rhs : lhs_1 + c ≤ lhs_2 + c ↔ lhs_1 ≤ lhs_2 := by
      exact add_le_add_right_iff

    rw [lhs_leeq_rhs]

    unfold lhs_1 lhs_2

    have simplify_rhs_1 :  a * (-b / (2 * a)) ^ 2 = b^2 /(4*a) := by
      rw [pow_two]
      rw [neg_div, neg_mul_neg, ←pow_two]
      field_simp
      ring

    rw [simplify_rhs_1]

    trace_state

    have simplify_rhs_2 :  b * (-b / (2 * a)) = - b^2 / (2 * a) := by
      rw [←mul_div_assoc, ←pow_two]
      ring

    rw [simplify_rhs_2]

    trace_state

    have simplify_rhs_3 : b ^ 2 / (4 * a) + -b ^ 2 / (2 * a) = - b^2 / (4*a) := by
      field_simp
      ring

    rw [simplify_rhs_3]

    trace_state

    have h_d_sub : d = beta / a := by
      rw [hd, hbeta, ha]
      unfold p_opt
      rw [symmetry_grad]

    rw [h_d_sub]

    trace_state

    have lhs_final :  a * (beta / a) ^ 2 + b * (beta / a) = - (beta^2)/a := by
      rw [←pow_two, ←mul_div_assoc]
      rw [←hb]
      rw [←pow_two, ←mul_div_assoc]
      field_simp
      ring

    rw [ lhs_final]

    rw [hb]

    rw [pow_two]

    rw [mul_pow]

    field_simp
    ring


    --simp only [neg_mul, even_two, Even.neg_pow, ge_iff_le]
    --ring
    --aesop?

    --rw [pow_two, mul_pow, ←mul_assoc]
    --simp?


    trace_state
