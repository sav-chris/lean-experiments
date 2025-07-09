import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

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



abbrev Pixel := ℕ × ℕ
abbrev Gradient := Pixel → ℝ × ℝ

def gradDot (f g : Gradient) (D : Finset Pixel) : ℝ :=
  ∑ x ∈ D,
    let (fx₁, fx₂) := f x
    let (gx₁, gx₂) := g x
    fx₁ * gx₁ + fx₂ * gx₂



def R (dI dB : Gradient) (D : Finset Pixel) (p : ℝ) : ℝ :=
  gradDot dI dI D - 2 * p * gradDot dB dI D + p ^ 2 * gradDot dB dB D

noncomputable def p_opt (dI dB : Gradient) (D : Finset Pixel) : ℝ :=
  gradDot dI dB D / gradDot dB dB D


/-
theorem R_has_minimum_at_p_opt
  (dI dB : Gradient) (D : Finset Pixel)
  (h : 0 < gradDot dB dB D) :
  ∀ p : ℝ, R dI dB D p ≥ R dI dB D (p_opt dI dB D) := by
  let a := gradDot dB dB D
  let b := gradDot dB dI D
  let c := gradDot dI dI D
  have ha : 0 < a := h
  apply quadratic_minimizer a b c ha
  --apply quadratic_minimizer a (-2 * b) c ha
-/


example (x : ℝ) :
    deriv (fun x ↦ x^2 ) x = 2 * x :=
  by
    simp



example (x : ℝ) :
    deriv (fun x ↦ 3 * x^2) x = 6 * x :=
  by
    simp
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



  --exact DifferentiableAt.pow (DifferentiableAt. ℝ x) 2



  --rw [differentiable_at.const_mul 3]
  --rw [differentiableAt_fun_id.pow]



/-
--def f(x: ℝ) := 3 * x ^ 2
--def g(x: ℝ) := 2 * x

lemma diff_distr (x : ℝ) : deriv ( fun y ↦ 3 * y ^ 2 + 2 * y ) x = deriv ( fun y ↦ 3 * y ^ 2 ) x + deriv ( fun y ↦ 2 * y ) x := by
  --exact deriv_add (λ y, 3 * y ^ 2) (λ y, 2 * y) x,
  let f := fun y ↦ 3 * y ^ 2
  let g := fun y ↦ 2 * y

  have h1 (x : ℝ) : DifferentiableAt ℝ f x := by
    exact differentiable_at.const_mul 3 (differentiable_at_id'.pow 2)

  have h2 (x : ℝ) : DifferentiableAt ℝ g x := by
    exact differentiable_at.const_mul 2 differentiable_at_id'

  --rw [←function.add_apply f g, deriv_add h1 h2]
  sorry

-/

/-
lemma poly_diff_example (x : ℝ) : deriv (f + g) x = 6 * x + 2 := by
  have h1 : DifferentiableAt ℝ f x := by
    apply DifferentiableAt.const_mul
    exact DifferentiableAt.pow differentiableAt_id 2

  have h2 : DifferentiableAt ℝ g x := by
    apply DifferentiableAt.const_mul
    exact differentiableAt_id

  rw [deriv_add h1 h2]
  unfold f g
  rw [deriv_const_mul, deriv_const_mul]
  rw [deriv_pow 2]
  trace_state
  simp?
  trace_state
  ring
  trace_state
-/


lemma h2 (x : ℝ) : DifferentiableAt ℝ (g) x := by
    apply DifferentiableAt.const_mul
    exact differentiableAt_id


lemma poly_diff_example (x : ℝ) : deriv (f + g) x = 6 * x + 2 := by
  have h1 : DifferentiableAt ℝ (f) x := by
    apply DifferentiableAt.const_mul
    apply differentiableAt_fun_id.pow
  have h2 : DifferentiableAt ℝ (g) x := by
    apply DifferentiableAt.const_mul
    exact differentiableAt_id

  have h_sq : DifferentiableAt ℝ (fun x ↦ x ^ 2) x := by
    exact DifferentiableAt.pow differentiableAt_id 2
  rw [deriv_add h1 h2]
  unfold f g
  rw [ deriv_const_mul 3 ]
  rw [deriv_pow 2 ]
  ring
  simp only [differentiableAt_fun_id, differentiableAt_const, deriv_fun_mul, deriv_id'', one_mul, deriv_const', mul_zero, add_zero]
  trace_state
  ring_nf
  trace_state


/-
  rw [deriv_const_mul 2 (differentiableAt_id x)]

  rw [deriv_const_mul, deriv_pow 2]
  rw [deriv_const_mul, deriv_id']
  rw [deriv_id]
-/





/-
lemma poly_diff_example (x : ℝ) : deriv (fun y ↦ 3 * y ^ 2 + 2 * y) x = 6 * x + 2:= by
  have h1 : DifferentiableAt ℝ (fun y ↦ 3 * y ^ 2) x := by
    sorry
  have h2 : DifferentiableAt ℝ (fun y ↦ 2 * y ) x := by
    sorry
  rw [←deriv_add (fun y ↦ 3 * y ^ 2) (fun y ↦ 2 * y)  h1 h2]
-/

/-
  rw [deriv_add (diff_pow_two x) ]
  rw [←diff_pow_two_const x]
  rw [deriv_const_mul]
  rw [deriv_id']
  ring
  apply differentiableAt_id
  apply diff_pow_two_const
-/



/-

example (x : ℝ) : deriv (fun y ↦ 3 * y ^ 2) x = 6 * x := by


  rw [deriv_const_mul]
  trace_state

  have diffh : DifferentiableAt ℝ (fun y ↦ y ^ 2) x := by
    sorry

  rw [deriv_pow 2]
  trace_state
  ring

-/
