import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith


import Mathlib.Data.Finset.Basic

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Linear

import Mathlib.Analysis.Calculus.Deriv.Add

import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts


import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory


open scoped BigOperators
open Set Real Filter Topology
open Function

open Classical
open scoped NNReal ENNReal
open List
open MeasureTheory


lemma scalar_mul_differentiable_within
  (B : ℝ → ℝ)
  (Ω : Set ℝ)
  (ρ x : ℝ)
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x :=
DifferentiableWithinAt.const_smul (hB x hx) ρ


lemma f_differentiable_within
  (I : ℝ → ℝ)
  (Ω : Set ℝ)
  (hI : DifferentiableOn ℝ I Ω)
  (x : ℝ)
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma deriv_distributes
    (I B : ℝ → ℝ)
    (x : ℝ )
    (Ω : Set ℝ)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ )
    (hΩ_open : IsOpen Ω)
    ( hΩ : x ∈ Ω )
:
    deriv (λ x ↦ I x - ρ • B x) x ^ 2 = (λ x ↦ (deriv I x ) - ρ • (deriv B x) ) x ^ 2
:= by
{
    apply congrArg (λ y => y ^ 2)

    let f := I
    let g := λ x ↦ ρ • B x

    let gg := λ x ↦ ρ • (deriv B x)

    have hn : Ω ∈ 𝓝 x := hΩ_open.mem_nhds hΩ
    have hf : DifferentiableWithinAt ℝ f Ω x := f_differentiable_within I Ω hI x hΩ
    have hg : DifferentiableWithinAt ℝ g Ω x := scalar_mul_differentiable_within B Ω ρ x hB hΩ
    have hf' : DifferentiableAt ℝ f x := hf.differentiableAt hn
    have hg' : DifferentiableAt ℝ g x := hg.differentiableAt hn
    have hB' : DifferentiableAt ℝ B x := (hB x hΩ).differentiableAt hn

    change deriv (λ x => f x - g x) x = (λ x ↦ (deriv f x ) - ρ • (deriv B x) ) x

    change deriv (λ x => f x - g x) x = (λ x ↦ (deriv f x ) - (gg x) ) x

    have ρBh : (deriv g x) = gg x := by
    {
        unfold gg
        unfold g
        simp_all only [smul_eq_mul, deriv_const_mul_field', f, g]
    }
    simp only [←ρBh]

    change deriv (f - g ) x = (deriv f x) - (deriv g x)

    rw [deriv_sub]

    apply hf'
    apply hg'
}


-- - e =ᵐ[volume.restrict Ω]
    --change (deriv (λ x => I x - ρ • B x) a ^ 2) =ᶠ[ae (volume.restrict Ω)] λ a => (λ x => deriv I x - ρ • deriv B x) a ^ 2
    --change (deriv (λ x => I x - ρ • B x) a ^ 2) = ᵐ[volume.restrict Ω] λ a => (λ x => deriv I x - ρ • deriv B x) a ^ 2
--filter_upwards [ae_restrict_mem (measurableSet_of_isOpen hΩ_open)] with a haΩ
   --funext
    --trace_state

    --apply EventuallyEq.pow
    --apply eventually_eq_of_mem (isOpen_mem_nhds hΩ_open)


lemma deriv_distributes_over_sub_within_integral_1
    (I B : ℝ → ℝ)
    (w h : ℝ)
    (hwh : w < h)
    (Ω : Set ℝ := Set.Ioo w h)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, deriv (λ x ↦ I x - ρ • B x) x ^ 2 =
    ∫ x in Ω, (λ x ↦ (deriv I x ) - ρ • (deriv B x) ) x ^ 2
:= by
{
    classical
    apply integral_congr_ae

    change (λ a => deriv (λ x => I x - ρ • B x) a ^ 2) =ᶠ[ae (volume.restrict Ω)] λ a => (λ x => deriv I x - ρ • deriv B x) a ^ 2

    change (λ a => deriv (λ x => I x - ρ • B x) a ^ 2) =ᵐ[volume.restrict Ω] λ a => (λ x => deriv I x - ρ • deriv B x) a ^ 2
    trace_state

    -- unfold Filter.EventuallyEq
    -- unfold Filter.Eventually

    change ∀ x ∈ Ω, (λ a => deriv (λ x => I x - ρ • B x) a ^ 2) = λ a => (λ x => deriv I x - ρ • deriv B x) a ^ 2

    have h_pointwise : ∀ x ∈ Ω, deriv (λ x ↦ I x - ρ • B x) x = deriv I x - ρ • deriv B x := by
      intro x hx
      apply (deriv_distributes I B x Ω hI hB ρ hΩ_open)

    --intro x hx




}


lemma deriv_distributes_over_sub_within_integral_2
    (I B : ℝ → ℝ)
    (w h : ℝ)
    (hwh : w < h)
    (Ω : Set ℝ := Set.Ioo w h)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, deriv (λ x ↦ I x - ρ • B x) x ^ 2 =
    ∫ x in Ω, (λ x ↦ (deriv I x ) - ρ • (deriv B x) ) x ^ 2
:= by
{
    apply integral_congr_ae

    change (λ a => deriv (λ x => I x - ρ • B x) a ^ 2) =ᵐ[volume.restrict Ω] λ a => (λ x => deriv I x - ρ • deriv B x) a ^ 2

    unfold Filter.EventuallyEq

    trace_state

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        deriv (λ x ↦ I x - ρ • B x) x = deriv I x - ρ • deriv B x
    := by
    {
        have h_mem : ∀ᵐ x ∂(volume.restrict Ω), x ∈ Ω := by
        {
            simp_all only [eventually_mem_set]

            change Ω ∈ ae (volume.restrict Ω)
            trace_state
            sorry
        }

        apply h_mem

        sorry
    }

    filter_upwards [h_deriv_eq] with x hx
    simp only [hx]

}


lemma deriv_distributes_over_sub_within_integral_3
    (I B : ℝ → ℝ)
    (w h : ℝ)
    (hwh : w < h)
    (Ω : Set ℝ := Set.Ioo w h)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, deriv (λ x ↦ I x - ρ • B x) x ^ 2 =
    ∫ x in Ω, (λ x ↦ (deriv I x ) - ρ • (deriv B x) ) x ^ 2
:= by
{
    classical
    apply integral_congr_ae

    have h_diff : DifferentiableOn ℝ (λ x ↦ I x - ρ • B x) Ω :=
      hI.sub (hB.const_smul ρ)

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        deriv (λ x ↦ I x - ρ • B x) x = deriv I x - ρ • deriv B x
    := by
    {
        trace_state
        sorry
    }

    filter_upwards [h_deriv_eq] with x hx
    simp only [hx]

    trace_state

}

------------------------------------------------------------------------------


lemma expand_squared (n : ℕ )( x y : (Fin n → ℝ) →L[ℝ] ℝ ) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * (∑ i, ( x - y ) (Pi.single i 1) • (x - y) (Pi.single i 1)) + ‖y‖ * ‖y‖
:= by
{

    sorry

}

------------------------------------------------------------------------------

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Data.Finset.Basic

import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace

open scoped BigOperators


def Ioo_nd (n : ℕ ) (w l : Fin n → ℝ) : Set (Fin n → ℝ) :=
    {x | ∀ i, w i < x i ∧ x i < l i}


lemma f_differentiable_within_nd {n : ℕ }
  (I : (Fin n → ℝ) → ℝ)
  (lower upper : (Fin n → ℝ))
  (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  Fin n → ℝ)
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd {n : ℕ }
  (B : (Fin n → ℝ) → ℝ)
  (lower upper : (Fin n → ℝ))
  (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
  (ρ : ℝ)
  (x : Fin n → ℝ)
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ



noncomputable def inner_prod_2ab_term
    {n : ℕ}
    (ρ : ℝ)
    (u : (Fin n → ℝ) →L[ℝ] ℝ)
    (B : (Fin n → ℝ) → ℝ)
    (x : (Fin n → ℝ))
:=
    (ρ • ∑ i, (u) (Pi.single i 1) • (fderiv ℝ B x) (Pi.single i 1))


noncomputable def grad {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  λ i ↦ fderiv ℝ f x (Pi.single i 1)

noncomputable def gradNorm {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
    (Norm.norm (grad f x))


noncomputable def S_n
    {n : ℕ }
    (I B : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ)
    (ρ : ℝ ) : Fin n → ℝ :=
    λ i ↦ ((grad I x i) - ρ • (grad B x i))

def f : (Fin 2 → ℝ) → ℝ := λ x ↦ x 0 ^ 2 + x 1 ^ 2
def g : (Fin 2 → ℝ) → ℝ := λ x ↦ x 0 + x 1
def x : Fin 2 → ℝ := ![1, 2]
def ρ : ℝ := 0.5

--#eval (S_n f g x ρ 0)
--#reduce S_n f g x ρ 1

--set_option diagnostics true
  --‖grad f x‖


-- \| \nabla I(x)-\rho \nabla B(x)\| ^2=\| \nabla I(x)\| ^2-2\rho \langle \nabla I(x),\nabla B(x)\rangle +\rho ^2\| \nabla B(x)\| ^2.




lemma S_n_vec
    {n : ℕ }
    (I B : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ)
    (ρ : ℝ )
:
    ∀ i : (Fin n), (S_n I B x ρ i) = (grad I x i) - ρ • (grad B x i)
:= by
{
    intro i
    rfl
}

lemma expand_squared_term_nd {n : ℕ }
    (I B : (Fin n → ℝ) → ℝ)
    (lower upper : (Fin n → ℝ))
    (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:

    ∫ x in Ω, (Norm.norm (S_n I B x ρ)) ^ 2 =
    ∫ x in Ω, (Norm.norm (fderiv ℝ I x) )^2 - 2 • ρ • (∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) + (ρ^2) • (Norm.norm (fderiv ℝ B x) )^2

/-
    ∫ x in Ω, (Norm.norm ((fderiv ℝ I x) - ρ • (fderiv ℝ B x ) ))^2 =
    ∫ x in Ω, (Norm.norm (fderiv ℝ I x) )^2 - 2 • ρ • (∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) + (ρ^2) • (Norm.norm (fderiv ℝ B x) )^2
-/
:= by
{
    let f := I
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (fderiv ℝ B x)
    #check Norm (Fin n → ℝ)
    #check Norm (ℝ →L[ℝ] ℝ)

    unfold S_n

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        fderiv ℝ (λ x ↦ I x - ρ • B x) x = fderiv ℝ I x - ρ • fderiv ℝ B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change fderiv ℝ (λ x => f x - g x) a = (λ x ↦ (fderiv ℝ f x ) - ρ • (fderiv ℝ B x) ) a

        change fderiv ℝ (λ x => f x - g x) a = (λ x ↦ (fderiv ℝ f x ) - (gg x) ) a

        have ρBh : (fderiv ℝ g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            rw [← fderiv_const_smul]
            simp_all only [differentiableAt_const, DifferentiableAt.fun_mul]
            rfl
            simp_all only [differentiableAt_const, DifferentiableAt.fun_mul]
        }
        simp only [←ρBh]

        change fderiv ℝ (f - g ) a = (fderiv ℝ f a) - (fderiv ℝ g a)

        rw [fderiv_sub]

        apply hf'
        apply hg'
    }

    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf

    trace_state
    #check Norm (Fin n → ℝ)

    let u := fderiv ℝ I x
    let v := ρ • fderiv ℝ B x

    have v_sq_h : ρ ^ 2 • (Norm.norm (fderiv ℝ B x)) ^ 2 = (Norm.norm v) ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    --unfold grad

    trace_state

    change (Norm.norm λ i ↦ ( grad I x i - ρ * grad B x i )) ^ 2 = -((ρ * ∑ x_1, (fderiv ℝ I x) (Pi.single x_1 1) * (fderiv ℝ B x) (Pi.single x_1 1)) * 2) + ρ ^ 2 * ‖fderiv ℝ B x‖ ^ 2 + ‖fderiv ℝ I x‖ ^ 2

    change (Norm.norm λ i ↦ (grad I x i - ρ * grad B x i )) ^ 2 = -((ρ * ∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) * 2) + ρ ^ 2 • (Norm.norm (fderiv ℝ B x)) ^ 2 + (Norm.norm u) ^ 2

    unfold grad

    change (Norm.norm λ i ↦ (grad I x i - ρ * grad B x i )) ^ 2 = -((ρ * ∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) * 2) + ρ ^ 2 • (Norm.norm (fderiv ℝ B x)) ^ 2 + (Norm.norm u) ^ 2

    trace_state

    unfold grad

    trace_state

    --change ‖fun i => (fderiv ℝ I x) (Pi.single i 1) - ρ * (fderiv ℝ B x) (Pi.single i 1)‖ ^ 2 = (Norm.norm u) ^ 2 - (ρ • ∑ i, (fderiv ℝ I x) (Pi.single i 1) • (fderiv ℝ B x) (Pi.single i 1)) * 2 + ρ ^ 2 • (Norm.norm (fderiv ℝ B x)) ^ 2
    --change (Norm.norm (u - v)) ^ 2 = (Norm.norm u) ^ 2 - (ρ • ∑ i, (fderiv ℝ I x) (Pi.single i 1) • (fderiv ℝ B x) (Pi.single i 1)) * 2 + ρ ^ 2 • (Norm.norm (fderiv ℝ B x)) ^ 2

    rw [v_sq_h]

    change (Norm.norm λ i ↦ (u (Pi.single i 1) - v (Pi.single i 1))) ^ 2 = -((ρ * ∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) * 2) + (Norm.norm v) ^ 2 + ‖u‖ ^ 2

    trace_state

    have h_unorm
        {n : ℕ} (w : (Fin n → ℝ) →L[ℝ] ℝ)
    :
        (norm w) ^ 2 = ‖w‖ ^ 2
    := by
    {
        rfl
    }

    have h_ρ_factor
        (ρ : ℝ)
        (u : (Fin n → ℝ) →L[ℝ] ℝ)
        (B : (Fin n → ℝ) → ℝ)
        (x : Fin n → ℝ)
    :
        (inner_prod_2ab_term ρ u B x) = (∑ i, (u) (Pi.single i 1) • ρ • (fderiv ℝ B x) (Pi.single i 1))
    := by
    {
        unfold inner_prod_2ab_term
        trace_state
        rw [Finset.smul_sum]

        change ∑ (x_1 : Fin n), ρ • u (Pi.single x_1 1) • (fderiv ℝ B x) (Pi.single x_1 1) = ∑ x_1, u (Pi.single x_1 1) • ρ • (fderiv ℝ B x) (Pi.single x_1 1)

        let c (x_1 : Fin n ) := (fderiv ℝ B x) (Pi.single x_1 1)

        change ∑ x_1, ρ • u (Pi.single x_1 1) • (c x_1) = ∑ x_1, u (Pi.single x_1 1) • ρ • (c x_1)

        let d (x_1 : Fin n ) := u (Pi.single x_1 1)

        change ∑ x_1, ρ • (d x_1) • (c x_1) = ∑ x_1, (d x_1) • ρ • (c x_1)

        rw [Finset.sum_congr]
        rfl

        intro x h

        let d_ : ℝ := (d x)
        let c_ : ℝ := (c x)

        change ρ • d_ • c_ = d_ • ρ • c_
        rw [smul_comm]
    }


    change (Norm.norm (u - v)) ^ 2 = (norm u) ^ 2 - (ρ • ∑ i, (u) (Pi.single i 1) • (fderiv ℝ B x) (Pi.single i 1)) • 2 + (Norm.norm v) ^ 2
    change (Norm.norm (u - v)) ^ 2 = (norm u) ^ 2 - (inner_prod_2ab_term ρ u B x) • 2 + (Norm.norm v) ^ 2

    trace_state
    rw [(h_ρ_factor ρ u B x)]

    change (Norm.norm (u - v)) ^ 2 = (Norm.norm u) ^ 2 - (∑ i, u (Pi.single i 1) • v (Pi.single i 1)) • 2 + (Norm.norm v) ^ 2
    trace_state

    --let E := ((Fin n → ℝ) →L[ℝ] ℝ)  -- ≃ₗᵢ[ℝ] (Fin n → ℝ)
                -- re ⟪x, x⟫
                --rw [←inner_self_eq_norm_sq]

    have h_1 : InnerProductSpace ℝ ((Fin n → ℝ) →L[ℝ] ℝ) := by
        refine
        {
            inner               := λ x y ↦ (∑ i, x (Pi.single i 1) • y (Pi.single i 1))
            norm_sq_eq_re_inner := by
            {
                intro x
                change ‖x‖ ^ 2 = RCLike.re (∑ i, x (Pi.single i 1) • x (Pi.single i 1))

                rw [pow_two]

                change (norm x) * (norm x) = RCLike.re (∑ i, x (Pi.single i 1) • x (Pi.single i 1))
                --unfold norm
                trace_state
                sorry
            }
            conj_inner_symm     := sorry
            add_left            := sorry
            smul_left           := sorry

        }



    rw [(norm_sub_sq_real) ]

    simp
    ring_nf


    let a := (∑ x, u (Pi.single x 1) * v (Pi.single x 1))
    let b := ⟪u, v⟫_ℝ

    change b * 2 = a * 2


    have h₂ : (2 : ℝ) ≠ 0 := by norm_num

    rw [←mul_right_inj' (by norm_num : (1/2 : ℝ) ≠ 0)]
    trace_state
    ring_nf
    trace_state

    unfold a b


    change (inner ℝ u v ) = ∑ x, u (Pi.single x 1) * v (Pi.single x 1)

    unfold inner


    trace_state

}


------------------------------------------------------------------------------


import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Data.Finset.Basic

import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace

open scoped BigOperators

/-
def hypercube (n : ℕ ) (w l : Fin n → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}
-/

def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}

/-
lemma expand_squared_term_nd_1 {n : ℕ }
    (I B : (Fin n → ℝ) → ℝ)
    (lower upper : (Fin n → ℝ))
    (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((fderiv ℝ I x) - ρ • (fderiv ℝ B x ) )‖^2 =
    ∫ x in Ω, ‖(fderiv ℝ I x)‖^2 - 2 • ρ • (∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) + (ρ^2) • ‖(fderiv ℝ B x)‖^2
:= by
{
    sorry
}
-/

/-
example (x : Fin 3 → ℝ) : ‖x‖ = Real.sqrt (∑ i, (x i)^2) := by
{
  simp [Norm.norm]
  trace_state
  -- unsolved goals
  -- x : Fin 3 → ℝ
  -- ⊢ ↑(Finset.univ.sup fun b => ‖x b‖₊) = √(∑ i, x i ^ 2)
  sorry
}
-/


example (x : EuclideanSpace ℝ (Fin 3)) : ‖x‖ = Real.sqrt (∑ i, (x i)^2) := by
{
    simp only [Norm.norm, Real.sqrt_eq_rpow]
    simp only
    [
        OfNat.ofNat_ne_zero,
        ↓reduceIte,
        ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofNat,
        rpow_ofNat,
        sq_abs,
        one_div
    ]
}


    -- x : EuclideanSpace ℝ (Fin 3)
    -- ⊢ (∑ x_1, x.ofLp x_1 ^ 2) ^ 2⁻¹ = √(∑ x_1, x.ofLp x_1 ^ 2)

/-
def hypercube {n : Type _} [Fintype n] (w l : EuclideanSpace ℝ n) : Set (EuclideanSpace ℝ n) :=
    {x | ∀ i, w i < x i ∧ x i < l i}

    -/


noncomputable def inner_prod_2ab_term
    {n : ℕ}
    (ρ : ℝ)
    --(u : (Fin n → ℝ) →L[ℝ] ℝ)
    (u : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    --(B : (Fin n → ℝ) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    --(x : (Fin n → ℝ))
:=
    (ρ • ∑ i, (u) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1))


lemma f_differentiable_within_nd {n : ℕ }
  (I : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ



--lemma expand_squared_term_nd {n : Type _} [Fintype n] [DecidableEq n]
lemma expand_squared_term_nd {n : ℕ}
    --(I B : (EuclideanSpace ℝ (Fin n)) → ℝ)
    (I B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    --(lower upper : (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((fderiv ℝ I x) - ρ • (fderiv ℝ B x ) )‖^2 =
    ∫ x in Ω, ‖(fderiv ℝ I x)‖^2 - 2 • ρ • (∑ i, (fderiv ℝ I x) (EuclideanSpace.single i 1) * (fderiv ℝ B x) (EuclideanSpace.single i 1)) + (ρ^2) • ‖(fderiv ℝ B x)‖^2
:= by
{

    let f := λ x ↦ (I x)
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (fderiv ℝ B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        fderiv ℝ (λ x ↦ I x - ρ • B x) x = fderiv ℝ I x - ρ • fderiv ℝ B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change fderiv ℝ (λ x => f x - g x) a = (λ x ↦ (fderiv ℝ f x ) - ρ • (fderiv ℝ B x) ) a

        change fderiv ℝ (λ x => f x - g x) a = (λ x ↦ (fderiv ℝ f x ) - (gg x) ) a

        have ρBh : (fderiv ℝ g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            rw [← fderiv_const_smul]
            simp_all only [differentiableAt_const, DifferentiableAt.fun_mul]
            rfl
            simp_all only [differentiableAt_const, DifferentiableAt.fun_mul]
        }
        simp only [←ρBh]

        change fderiv ℝ (f - g ) a = (fderiv ℝ f a) - (fderiv ℝ g a)

        rw [fderiv_sub]

        apply hf'
        apply hg'
    }


    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf


    let u := fderiv ℝ I x
    let v := ρ • fderiv ℝ B x

    have v_sq_h : ρ ^ 2 • ‖(fderiv ℝ B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (fderiv ℝ I x) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1)) * 2 + ρ ^ 2 • ‖(fderiv ℝ B x)‖ ^ 2
    rw [v_sq_h]


    have h_unorm
        {n : ℕ} (w : (Fin n → ℝ) →L[ℝ] ℝ)
    :
        (norm w) ^ 2 = ‖w‖ ^ 2
    := by
    {
        rfl
    }

    have h_ρ_factor
        (ρ : ℝ)
        --(u : (Fin n → ℝ) →L[ℝ] ℝ)
        (u : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (x : EuclideanSpace ℝ (Fin n))
    :
        (inner_prod_2ab_term ρ u B x) = (∑ i, (u) (EuclideanSpace.single i 1) • ρ • (fderiv ℝ B x) (EuclideanSpace.single i 1))
    := by
    {
        unfold inner_prod_2ab_term
        trace_state
        rw [Finset.smul_sum]

        change ∑ (x_1 : Fin n), ρ • u (EuclideanSpace.single x_1 1) • (fderiv ℝ B x) (EuclideanSpace.single x_1 1) = ∑ x_1, u (EuclideanSpace.single x_1 1) • ρ • (fderiv ℝ B x) (EuclideanSpace.single x_1 1)

        let c (x_1 : Fin n ) := (fderiv ℝ B x) (EuclideanSpace.single x_1 1)

        change ∑ x_1, ρ • u (EuclideanSpace.single x_1 1) • (c x_1) = ∑ x_1, u (EuclideanSpace.single x_1 1) • ρ • (c x_1)

        let d (x_1 : Fin n ) := u (EuclideanSpace.single x_1 1)

        change ∑ x_1, ρ • (d x_1) • (c x_1) = ∑ x_1, (d x_1) • ρ • (c x_1)

        rw [Finset.sum_congr]
        rfl

        intro x h

        let d_ : ℝ := (d x)
        let c_ : ℝ := (c x)

        change ρ • d_ • c_ = d_ • ρ • c_
        rw [smul_comm]
    }


    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (u) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2
    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (inner_prod_2ab_term ρ u B x) • 2 + ‖v‖ ^ 2

    trace_state
    rw [(h_ρ_factor ρ u B x)]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, u (EuclideanSpace.single i 1) • v (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2



    --rw [(norm_sub_sq_real) ]

    trace_state

}



-------------------------------------------------------------------------------------

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace
open scoped BigOperators


def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}


example (x : EuclideanSpace ℝ (Fin 3)) : ‖x‖ = Real.sqrt (∑ i, (x i)^2) := by
{
    simp only [Norm.norm, Real.sqrt_eq_rpow]
    simp only
    [
        OfNat.ofNat_ne_zero,
        ↓reduceIte,
        ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofNat,
        rpow_ofNat,
        sq_abs,
        one_div
    ]
}


noncomputable def inner_prod_2ab_term_euclidean
    {n : ℕ}
    (ρ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    (ρ • ∑ i, (u) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1))


lemma f_differentiable_within_nd_euclidean {n : ℕ }
  (I : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd_euclidean {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ

-- set_option diagnostics true

--  EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ
noncomputable def grad {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin n)) := (fderiv ℝ f x)



lemma expand_squared_term_nd {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((fderiv ℝ I x) - ρ • (fderiv ℝ B x ) )‖^2 =
    --∫ x in Ω, ‖(fderiv ℝ I x)‖^2 - 2 • ρ • ⟪fderiv ℝ I x, fderiv ℝ B x⟫_ℝ + (ρ^2) • ‖(fderiv ℝ B x)‖^2

    ∫ x in Ω, ‖(fderiv ℝ I x)‖^2 - 2 • ρ • (∑ i, (fderiv ℝ I x) (EuclideanSpace.single i 1) * (fderiv ℝ B x) (EuclideanSpace.single i 1)) + (ρ^2) • ‖(fderiv ℝ B x)‖^2
:= by
{

    let f := λ x ↦ (I x)
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (fderiv ℝ B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        fderiv ℝ (λ x ↦ I x - ρ • B x) x = fderiv ℝ I x - ρ • fderiv ℝ B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd_euclidean I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd_euclidean B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change fderiv ℝ (λ x => f x - g x) a = (λ x ↦ (fderiv ℝ f x ) - ρ • (fderiv ℝ B x) ) a

        change fderiv ℝ (λ x => f x - g x) a = (λ x ↦ (fderiv ℝ f x ) - (gg x) ) a

        have ρBh : (fderiv ℝ g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            rw [← fderiv_const_smul]
            simp_all only [differentiableAt_const, DifferentiableAt.fun_mul]
            rfl
            simp_all only [differentiableAt_const, DifferentiableAt.fun_mul]
        }
        simp only [←ρBh]

        change fderiv ℝ (f - g ) a = (fderiv ℝ f a) - (fderiv ℝ g a)

        rw [fderiv_sub]

        apply hf'
        apply hg'
    }


    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf


    let u := fderiv ℝ I x
    let v := ρ • fderiv ℝ B x

    have v_sq_h : ρ ^ 2 • ‖(fderiv ℝ B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (fderiv ℝ I x) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1)) * 2 + ρ ^ 2 • ‖(fderiv ℝ B x)‖ ^ 2
    rw [v_sq_h]


    have h_unorm
        {n : ℕ} (w : (Fin n → ℝ) →L[ℝ] ℝ)
    :
        (norm w) ^ 2 = ‖w‖ ^ 2
    := by
    {
        rfl
    }

    have h_ρ_factor
        (ρ : ℝ)
        (u : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (x : EuclideanSpace ℝ (Fin n))
    :
        (inner_prod_2ab_term_euclidean ρ u B x) = (∑ i, (u) (EuclideanSpace.single i 1) • ρ • (fderiv ℝ B x) (EuclideanSpace.single i 1))
    := by
    {
        unfold inner_prod_2ab_term_euclidean
        trace_state
        rw [Finset.smul_sum]

        change ∑ (x_1 : Fin n), ρ • u (EuclideanSpace.single x_1 1) • (fderiv ℝ B x) (EuclideanSpace.single x_1 1) = ∑ x_1, u (EuclideanSpace.single x_1 1) • ρ • (fderiv ℝ B x) (EuclideanSpace.single x_1 1)

        let c (x_1 : Fin n ) := (fderiv ℝ B x) (EuclideanSpace.single x_1 1)

        change ∑ x_1, ρ • u (EuclideanSpace.single x_1 1) • (c x_1) = ∑ x_1, u (EuclideanSpace.single x_1 1) • ρ • (c x_1)

        let d (x_1 : Fin n ) := u (EuclideanSpace.single x_1 1)

        change ∑ x_1, ρ • (d x_1) • (c x_1) = ∑ x_1, (d x_1) • ρ • (c x_1)

        rw [Finset.sum_congr]
        rfl

        intro x h

        let d_ : ℝ := (d x)
        let c_ : ℝ := (c x)

        change ρ • d_ • c_ = d_ • ρ • c_
        rw [smul_comm]
    }


    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (u) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2
    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (inner_prod_2ab_term_euclidean ρ u B x) • 2 + ‖v‖ ^ 2

    trace_state
    rw [(h_ρ_factor ρ u B x)]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, u (EuclideanSpace.single i 1) • v (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2

    have h_inner_prod_space : InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
    {
        refine
        {
            inner               := λ x y ↦ (∑ i, x (EuclideanSpace.single i 1) • y (EuclideanSpace.single i 1))
            --inner               := λ x y ↦ ⟪x, y⟫_ℝ
            norm_sq_eq_re_inner := by
            {
                intro x
                change ‖x‖ ^ 2 = RCLike.re (∑ i, x (EuclideanSpace.single i 1) • x (EuclideanSpace.single i 1))

                rw [pow_two]

                change ‖x‖ * ‖x‖ = RCLike.re (∑ i, x (EuclideanSpace.single i 1) • x (EuclideanSpace.single i 1))
                -- unfold norm
                simp only [Norm.norm]


                --simp_all only [smul_eq_mul, ContinuousLinearMap.fderiv, ae_restrict_eq, implies_true, map_sum,
                --  RCLike.mul_re, RCLike.re_to_real, RCLike.im_to_real, mul_zero, sub_zero, v]

                --rw [inner_self_eq_sum]

                trace_state
            }
            conj_inner_symm     := sorry
            add_left            := sorry
            smul_left           := sorry

        }
    }


    rw [(norm_sub_sq_real) ]

    trace_state

    change ‖u‖ ^ 2 - 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, u (EuclideanSpace.single i 1) • v (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2

    abel

    trace_state
    --unfold Norm.norm
    --unfold inner
    trace_state


}

-------------------------------------------------------------------------------------

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace
open scoped BigOperators


def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}



noncomputable def inner_prod_2ab_term_euclidean
    {n : ℕ}
    (ρ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    (ρ • ∑ i, (u) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1))


lemma f_differentiable_within_nd_euclidean {n : ℕ }
  (I : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd_euclidean {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ



lemma expand_squared_term_nd {n : ℕ}
    -- May need to use I B : EuclideanSpace ℝ (Fin n) → ℝ

    (I B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((fderiv ℝ I x) - ρ • (fderiv ℝ B x ) )‖^2 =
    --∫ x in Ω, ‖(fderiv ℝ I x)‖^2 - 2 • ρ • ⟪fderiv ℝ I x, fderiv ℝ B x⟫_ℝ + (ρ^2) • ‖(fderiv ℝ B x)‖^2

    ∫ x in Ω, ‖(fderiv ℝ I x)‖^2 - 2 • ρ • (∑ i, (fderiv ℝ I x) (EuclideanSpace.single i 1) * (fderiv ℝ B x) (EuclideanSpace.single i 1)) + (ρ^2) • ‖(fderiv ℝ B x)‖^2
:= by
{

    let f := λ x ↦ (I x)
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (fderiv ℝ B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        fderiv ℝ (λ x ↦ I x - ρ • B x) x = fderiv ℝ I x - ρ • fderiv ℝ B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd_euclidean I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd_euclidean B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change fderiv ℝ (λ x => f x - g x) a = (λ x ↦ (fderiv ℝ f x ) - ρ • (fderiv ℝ B x) ) a

        change fderiv ℝ (λ x => f x - g x) a = (λ x ↦ (fderiv ℝ f x ) - (gg x) ) a

        have ρBh : (fderiv ℝ g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            rw [← fderiv_const_smul]
            simp_all only [differentiableAt_const, DifferentiableAt.fun_mul]
            rfl
            simp_all only [differentiableAt_const, DifferentiableAt.fun_mul]
        }
        simp only [←ρBh]

        change fderiv ℝ (f - g ) a = (fderiv ℝ f a) - (fderiv ℝ g a)

        rw [fderiv_sub]

        apply hf'
        apply hg'
    }


    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf


    let u := fderiv ℝ I x
    let v := ρ • fderiv ℝ B x

    have v_sq_h : ρ ^ 2 • ‖(fderiv ℝ B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (fderiv ℝ I x) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1)) * 2 + ρ ^ 2 • ‖(fderiv ℝ B x)‖ ^ 2
    rw [v_sq_h]


    have h_unorm
        {n : ℕ} (w : (Fin n → ℝ) →L[ℝ] ℝ)
    :
        (norm w) ^ 2 = ‖w‖ ^ 2
    := by
    {
        rfl
    }

    have h_ρ_factor
        (ρ : ℝ)
        (u : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (x : EuclideanSpace ℝ (Fin n))
    :
        (inner_prod_2ab_term_euclidean ρ u B x) = (∑ i, (u) (EuclideanSpace.single i 1) • ρ • (fderiv ℝ B x) (EuclideanSpace.single i 1))
    := by
    {
        unfold inner_prod_2ab_term_euclidean

        rw [Finset.smul_sum]

        change ∑ (x_1 : Fin n), ρ • u (EuclideanSpace.single x_1 1) • (fderiv ℝ B x) (EuclideanSpace.single x_1 1) = ∑ x_1, u (EuclideanSpace.single x_1 1) • ρ • (fderiv ℝ B x) (EuclideanSpace.single x_1 1)

        let c (x_1 : Fin n ) := (fderiv ℝ B x) (EuclideanSpace.single x_1 1)

        change ∑ x_1, ρ • u (EuclideanSpace.single x_1 1) • (c x_1) = ∑ x_1, u (EuclideanSpace.single x_1 1) • ρ • (c x_1)

        let d (x_1 : Fin n ) := u (EuclideanSpace.single x_1 1)

        change ∑ x_1, ρ • (d x_1) • (c x_1) = ∑ x_1, (d x_1) • ρ • (c x_1)

        rw [Finset.sum_congr]
        rfl

        intro x h

        let d_ : ℝ := (d x)
        let c_ : ℝ := (c x)

        change ρ • d_ • c_ = d_ • ρ • c_
        rw [smul_comm]
    }


    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (u) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2
    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (inner_prod_2ab_term_euclidean ρ u B x) • 2 + ‖v‖ ^ 2

    rw [(h_ρ_factor ρ u B x)]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, u (EuclideanSpace.single i 1) • v (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2

    have h_inner_prod_space : InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
    {
        refine
        {
            inner               := λ x y ↦ (∑ i, x (EuclideanSpace.single i 1) • y (EuclideanSpace.single i 1))
            norm_sq_eq_re_inner := by
            {
                intro x
                change ‖x‖ ^ 2 = RCLike.re (∑ i, x (EuclideanSpace.single i 1) • x (EuclideanSpace.single i 1))

                rw [pow_two]

                change ‖x‖ * ‖x‖ = RCLike.re (∑ i, x (EuclideanSpace.single i 1) • x (EuclideanSpace.single i 1))
                simp only [Norm.norm]


                trace_state
            }
            conj_inner_symm     := by
            {
                intro x y
                simp only [starRingEnd_apply]

                have hstar : ∀ r : ℝ, star r = r := by intro r; simp only [star_trivial]

                rw [hstar]
                simp [mul_comm]
            }
            add_left            := by
            {
                intro x y z
                simp only [ContinuousLinearMap.add_apply, smul_eq_mul]

                simp_all only [smul_eq_mul, ContinuousLinearMap.fderiv, ae_restrict_eq, implies_true, v]

                change ∑ x_1, (x (EuclideanSpace.single x_1 1) + y (EuclideanSpace.single x_1 1)) * z (EuclideanSpace.single x_1 1) =
                ∑ x_1, x (EuclideanSpace.single x_1 1) * z (EuclideanSpace.single x_1 1) + ∑ x, y (EuclideanSpace.single x 1) * z (EuclideanSpace.single x 1)

                change
                  ∑ i,
                      (x (EuclideanSpace.single i 1) + y (EuclideanSpace.single i 1))
                        * z (EuclideanSpace.single i 1)
                    =
                    ∑ i, x (EuclideanSpace.single i 1) * z (EuclideanSpace.single i 1) +
                      ∑ i, y (EuclideanSpace.single i 1) * z (EuclideanSpace.single i 1)

                have h_mul :
                  ∀ i,
                    (x (EuclideanSpace.single i 1) + y (EuclideanSpace.single i 1))
                        * z (EuclideanSpace.single i 1)
                      =
                    x (EuclideanSpace.single i 1) * z (EuclideanSpace.single i 1)
                      +
                    y (EuclideanSpace.single i 1) * z (EuclideanSpace.single i 1)
                := by
                {
                    intro i
                    set a := x (EuclideanSpace.single i 1) with ha
                    set b := y (EuclideanSpace.single i 1) with hb
                    set c := z (EuclideanSpace.single i 1) with hc
                    ring
                }

                simp [h_mul, Finset.sum_add_distrib]
            }
            smul_left           := by
            {
                change ∀ (x y : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (r : ℝ), ∑ i, (r • x) (EuclideanSpace.single i 1) • y (EuclideanSpace.single i 1) = (starRingEnd ℝ) r * ∑ i, x (EuclideanSpace.single i 1) • y (EuclideanSpace.single i 1)
                intro x y r
                change
                  ∑ i,
                      (r • x) (EuclideanSpace.single i 1) •
                        y (EuclideanSpace.single i 1)
                    =
                      (starRingEnd ℝ) r *
                        ∑ i, x (EuclideanSpace.single i 1) • y (EuclideanSpace.single i 1)

                have hstar : (starRingEnd ℝ) r = r := by simp only [conj_trivial]

                -- Rewrite `(r • x) v = r * x v`
                simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hstar, Finset.mul_sum]
                simp only [mul_assoc]
            }

        }
    }


    rw [(norm_sub_sq_real) ]

    trace_state

    change ‖u‖ ^ 2 - 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, u (EuclideanSpace.single i 1) • v (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2

    simp only [smul_eq_mul, add_left_inj, sub_right_inj]



    rw [←mul_right_inj' (by norm_num : (1/2 : ℝ) ≠ 0)]
    ring

    unfold inner
    trace_state



}



noncomputable def custom_inner_product
    {n : ℕ }
    (u v : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    --(x : EuclideanSpace ℝ (Fin n))
:=
    (∑ i, u (EuclideanSpace.single i 1) * v (EuclideanSpace.single i 1))


--------------------------------------------------------------------------

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace
open scoped BigOperators


def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}



noncomputable def inner_prod_2ab_term_euclidean
    {n : ℕ}
    (ρ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) )
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    (ρ • ∑ i, (u i) • (gradient B x i) )


lemma f_differentiable_within_nd_euclidean {n : ℕ }
  (I : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd_euclidean {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ


    --(hρ : ρ ≠ 0 )
lemma grad_const_mul
    {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (a : EuclideanSpace ℝ (Fin n))
:
    gradient (fun x => ρ • B x) a = ρ • (gradient B a)
:= by
{
    --unfold gradient
    --let R := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    --have hR : R = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm := rfl
    --change R (fderiv ℝ (fun x => ρ • B x) a) = ρ • R (fderiv ℝ B a)
    --rw[←fderiv_const_smul]
    trace_state
    sorry
}

lemma grad_f_sub_g
    {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a : EuclideanSpace ℝ (Fin n))
:
    gradient (f - g) a = gradient f a - gradient g a
:= by
{
    sorry
}
    --refine PiLp.ext ?_
    --refine Eq.symm (PiLp.ext ?_)
    --refine (inv_smul_eq_iff₀ ?_).mp ?_
    --refine PiLp.ext ?_
    --intro i

lemma expand_squared_term_nd {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((gradient I x) - ρ • (gradient B x ) )‖^2 =
    ∫ x in Ω, ‖(gradient I x)‖^2 - 2 • ρ • (∑ i, (gradient I x i) * (gradient B x i)) + (ρ^2) • ‖(gradient B x)‖^2

:= by
{

    let f := λ x ↦ (I x)
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (gradient B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        gradient (λ x ↦ I x - ρ • B x) x = gradient I x - ρ • gradient B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd_euclidean I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd_euclidean B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change gradient (λ x => f x - g x) a = (λ x ↦ (gradient f x ) - ρ • (gradient B x) ) a

        change gradient (λ x => f x - g x) a = (λ x ↦ (gradient f x ) - (gg x) ) a

        have ρBh : (gradient g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            simp only [← smul_eq_mul]
            simp only [grad_const_mul]
        }
        simp only [←ρBh]

        change gradient (f - g ) a = (gradient f a) - (gradient g a)

        apply grad_f_sub_g
    }

    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf


    let u := gradient I x
    let v := ρ • gradient B x

    have v_sq_h : ρ ^ 2 • ‖(gradient B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (gradient I x i) • (gradient B x i)) * 2 + ρ ^ 2 • ‖(gradient B x)‖ ^ 2
    rw [v_sq_h]

    have h_ρ_factor
        (ρ : ℝ)
        (u : EuclideanSpace ℝ (Fin n))
        (B : EuclideanSpace ℝ (Fin n) → ℝ)
        (x : EuclideanSpace ℝ (Fin n))
    :
        (inner_prod_2ab_term_euclidean ρ u B x) = (∑ i, (u i) • ρ • (gradient B x i))
    := by
    {
        unfold inner_prod_2ab_term_euclidean

        rw [Finset.smul_sum]

        change ∑ (x_1 : Fin n), ρ • (u x_1) • ((gradient B x) x_1) = ∑ x_1, (u x_1) • ρ • ((gradient B x) x_1)

        let c (x_1 : Fin n ) := ((gradient B x) x_1 )

        change ∑ x_1, ρ • (u x_1) • (c x_1) = ∑ x_1, (u x_1) • ρ • (c x_1)

        let d (x_1 : Fin n ) := (u x_1)

        change ∑ x_1, ρ • (d x_1) • (c x_1) = ∑ x_1, (d x_1) • ρ • (c x_1)

        rw [Finset.sum_congr]
        rfl

        intro x h

        let d_ : ℝ := (d x)
        let c_ : ℝ := (c x)

        change ρ • d_ • c_ = d_ • ρ • c_
        rw [smul_comm]
    }


    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (u i) • (gradient B x i)) • 2 + ‖v‖ ^ 2
    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (inner_prod_2ab_term_euclidean ρ u B x) • 2 + ‖v‖ ^ 2

    rw [(h_ρ_factor ρ u B x)]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    have h_inner_prod_space : InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n) ) := by
    {
        refine
        {
            inner               := λ x y ↦ (∑ i, (x i) • (y i))
            norm_sq_eq_re_inner := by
            {
                intro x
                change ‖x‖ ^ 2 = RCLike.re (∑ i, (x i) • (x i))

                rw [pow_two]

                change ‖x‖ * ‖x‖ = RCLike.re (∑ i, (x i) • (x i))
                --simp only [Norm.norm]
                trace_state
            }
            conj_inner_symm     := by
            {
                intro x y
                simp only [starRingEnd_apply]

                have hstar : ∀ r : ℝ, star r = r := by intro r; simp only [star_trivial]

                rw [hstar]
                simp [mul_comm]
            }
            add_left            := by
            {
                intro x y z
                simp only [smul_eq_mul]

                simp_all only [smul_eq_mul, ae_restrict_eq, v]

                change ∑ x_1, ((x x_1) + (y x_1)) * (z x_1) = ∑ x_1, (x x_1) * (z x_1) + ∑ x_1, (y x_1) * (z x_1)

                have h_mul :
                  ∀ i,
                    ((x i) + (y i)) * (z i)
                      =
                    (x i) * (z i)
                      +
                    (y i) * (z i)
                := by
                {
                    intro i
                    ring
                }

                simp [h_mul, Finset.sum_add_distrib]
            }
            smul_left           := by
            {
                intro x y r
                have hstar : (starRingEnd ℝ) r = r := by simp only [conj_trivial]

                -- Rewrite `(r • x) v = r * x v`
                simp only [smul_eq_mul, hstar, Finset.mul_sum]
                trace_state
                --simp only [mul_assoc]
                sorry
            }

        }
    }


    change ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    trace_state

    rw [(norm_sub_sq_real) ]

    trace_state

    change ‖u‖ ^ 2 - 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    simp only [smul_eq_mul, add_left_inj, sub_right_inj]



    rw [←mul_right_inj' (by norm_num : (1/2 : ℝ) ≠ 0)]
    ring

    unfold inner
    trace_state



}

------------------------------------------------------------------------------------------

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Mathlib.Analysis.Normed.Operator.LinearIsometry

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace
open scoped BigOperators


def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}



noncomputable def inner_prod_2ab_term_euclidean
    {n : ℕ}
    (ρ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) )
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    (ρ • ∑ i, (u i) • (gradient B x i) )


lemma f_differentiable_within_nd_euclidean {n : ℕ }
  (I : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd_euclidean {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ


    --simp [map_smul]
    --unfold gradient
    --let R := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    --have hR : R = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm := rfl
    --change R (fderiv ℝ (fun x => ρ • B x) a) = ρ • R (fderiv ℝ B a)
    --rw[←fderiv_const_smul]
-- map_nsmul  f (n • a) = n • f a

example {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hB : DifferentiableAt ℝ B a)
:
    fderiv ℝ (fun x => ρ • B x) a = ρ • fderiv ℝ B a
:= by
{
    apply fderiv_const_smul (𝕜 := ℝ) (f := B) (c := ρ)
    apply hB
}

    --(hρ : ρ ≠ 0 )
lemma grad_const_mul
    {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hB :  DifferentiableAt ℝ B a)
:
    gradient (fun x => ρ • B x) a = ρ • (gradient B a)
:= by
{
    --simp [gradient, fderiv_const_smul a hB, map_smul]

    simp [gradient ]

    trace_state
    -- LinearIsometry.map_smul
  /-
    simp only [gradient]
    let M := λ x ↦ (B x)

    have hM : DifferentiableAt ℝ M a := by sorry

    change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (fun x => ρ • M x) a) =
  ρ • (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ M a)

    apply (fderiv_const_smul hM ρ  )
    -/

    /-
    simp only [gradient]
    let R := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm

    change R (fderiv ℝ (fun x => ρ • B x) a) = ρ • R (fderiv ℝ B a)

    let M := λ x ↦ (B x)

    change R (fderiv ℝ (fun x => ρ • (M x)) a) = ρ • R (fderiv ℝ M a)
    let f := λ x a ↦ (R (fderiv ℝ x a))

    change (f (fun x ↦ ρ • (M x)) a) = ρ • (f M a)

    --apply (fderiv_const_smul hB )
    trace_state
    -/

    -- exact fderiv_const_smul (𝕜 := ℝ) (f := B) (c := ρ)

    /-
    let f := λ x ↦ (B x)
    change gradient (fun x => ρ • f x) a = ρ • (gradient f a)
    simp only [gradient]

    have hf : DifferentiableAt ℝ f a := by sorry

    exact fderiv_const_smul (𝕜 := ℝ) (f := B) (c := ρ)


    rw [ (fderiv_const_smul hf ρ) ]

    trace_state
-/
    /-
    -- need to get in the formf (c • x) = c • f x
    let f := ...
    let c := ...
    let ...
    apply map_smul
    ...
    -/
}

lemma grad_f_sub_g
    {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hf :  DifferentiableAt ℝ f a)
    (hg :  DifferentiableAt ℝ g a)
:
    gradient (f - g) a = gradient f a - gradient g a
:= by
{
    simp only [gradient]
    rw [fderiv_sub hf hg]

    simp_all only [map_sub]
}

lemma expand_squared_term_nd {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((gradient I x) - ρ • (gradient B x ) )‖^2 =
    ∫ x in Ω, ‖(gradient I x)‖^2 - 2 • ρ • (∑ i, (gradient I x i) * (gradient B x i)) + (ρ^2) • ‖(gradient B x)‖^2

:= by
{

    let f := λ x ↦ (I x)
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (gradient B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        gradient (λ x ↦ I x - ρ • B x) x = gradient I x - ρ • gradient B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd_euclidean I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd_euclidean B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change gradient (λ x => f x - g x) a = (λ x ↦ (gradient f x ) - ρ • (gradient B x) ) a

        change gradient (λ x => f x - g x) a = (λ x ↦ (gradient f x ) - (gg x) ) a

        have ρBh : (gradient g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            simp only [← smul_eq_mul]
            simp only [grad_const_mul]
        }
        simp only [←ρBh]

        change gradient (f - g ) a = (gradient f a) - (gradient g a)

        apply (grad_f_sub_g f g a hf' hg')
    }

    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf


    let u := gradient I x
    let v := ρ • gradient B x

    have v_sq_h : ρ ^ 2 • ‖(gradient B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (gradient I x i) • (gradient B x i)) * 2 + ρ ^ 2 • ‖(gradient B x)‖ ^ 2
    rw [v_sq_h]

    have h_ρ_factor
        (ρ : ℝ)
        (u : EuclideanSpace ℝ (Fin n))
        (B : EuclideanSpace ℝ (Fin n) → ℝ)
        (x : EuclideanSpace ℝ (Fin n))
    :
        (inner_prod_2ab_term_euclidean ρ u B x) = (∑ i, (u i) • ρ • (gradient B x i))
    := by
    {
        unfold inner_prod_2ab_term_euclidean

        rw [Finset.smul_sum]

        change ∑ (x_1 : Fin n), ρ • (u x_1) • ((gradient B x) x_1) = ∑ x_1, (u x_1) • ρ • ((gradient B x) x_1)

        let c (x_1 : Fin n ) := ((gradient B x) x_1 )

        change ∑ x_1, ρ • (u x_1) • (c x_1) = ∑ x_1, (u x_1) • ρ • (c x_1)

        let d (x_1 : Fin n ) := (u x_1)

        change ∑ x_1, ρ • (d x_1) • (c x_1) = ∑ x_1, (d x_1) • ρ • (c x_1)

        rw [Finset.sum_congr]
        rfl

        intro x h

        let d_ : ℝ := (d x)
        let c_ : ℝ := (c x)

        change ρ • d_ • c_ = d_ • ρ • c_
        rw [smul_comm]
    }


    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (u i) • (gradient B x i)) • 2 + ‖v‖ ^ 2
    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (inner_prod_2ab_term_euclidean ρ u B x) • 2 + ‖v‖ ^ 2

    rw [(h_ρ_factor ρ u B x)]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    have h_inner_prod_space : InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n) ) := by
    {
        refine
        {
            inner               := λ x y ↦ (∑ i, (x i) • (y i))
            norm_sq_eq_re_inner := by
            {
                intro x
                change ‖x‖ ^ 2 = RCLike.re (∑ i, (x i) • (x i))

                rw [pow_two]

                change ‖x‖ * ‖x‖ = RCLike.re (∑ i, (x i) • (x i))
                --simp only [Norm.norm]
                trace_state
            }
            conj_inner_symm     := by
            {
                intro x y
                simp only [starRingEnd_apply]

                have hstar : ∀ r : ℝ, star r = r := by intro r; simp only [star_trivial]

                rw [hstar]
                simp [mul_comm]
            }
            add_left            := by
            {
                intro x y z
                simp only [smul_eq_mul]

                simp_all only [smul_eq_mul, ae_restrict_eq, v]

                change ∑ x_1, ((x x_1) + (y x_1)) * (z x_1) = ∑ x_1, (x x_1) * (z x_1) + ∑ x_1, (y x_1) * (z x_1)

                have h_mul :
                  ∀ i,
                    ((x i) + (y i)) * (z i)
                      =
                    (x i) * (z i)
                      +
                    (y i) * (z i)
                := by
                {
                    intro i
                    ring
                }

                simp [h_mul, Finset.sum_add_distrib]
            }
            smul_left           := by
            {
                intro x y r
                have hstar : (starRingEnd ℝ) r = r := by simp only [conj_trivial]

                -- Rewrite `(r • x) v = r * x v`
                simp only [smul_eq_mul, hstar, Finset.mul_sum]
                trace_state
                --simp only [mul_assoc]
                sorry
            }

        }
    }


    change ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    trace_state

    rw [(norm_sub_sq_real) ]

    trace_state

    change ‖u‖ ^ 2 - 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    simp only [smul_eq_mul, add_left_inj, sub_right_inj]



    rw [←mul_right_inj' (by norm_num : (1/2 : ℝ) ≠ 0)]
    ring

    unfold inner
    trace_state



}

------------------------------------------------------------------------------------------


import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Mathlib.Analysis.Normed.Operator.LinearIsometry

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace
open scoped BigOperators


def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}



noncomputable def inner_prod_2ab_term_euclidean
    {n : ℕ}
    (ρ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) )
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    (ρ • ∑ i, (u i) • (gradient B x i) )


lemma f_differentiable_within_nd_euclidean {n : ℕ }
  (I : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd_euclidean {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ


lemma grad_const_mul
    {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hB :  DifferentiableAt ℝ B a)
:
    gradient (fun x => ρ • B x) a = ρ • (gradient B a)
:= by
{
    simp only [gradient]

    let f := λ x ↦ (B x)
    have hf :  DifferentiableAt ℝ f a := by
    {
        unfold f
        fun_prop
    }

    change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (fun x => ρ • (f x)) a) =
  ρ • (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f a)

    have hhf : (fderiv ℝ (fun x => ρ • (f x)) a) = ρ • (fderiv ℝ f a) := by
    {
        rw [← (fderiv_const_smul hf ρ)]
        rfl
    }

    simp only [hhf]
    simp_all only [smul_eq_mul, map_smul, f]
}

lemma grad_f_sub_g
    {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hf :  DifferentiableAt ℝ f a)
    (hg :  DifferentiableAt ℝ g a)
:
    gradient (f - g) a = gradient f a - gradient g a
:= by
{
    simp only [gradient]
    rw [fderiv_sub hf hg]
    simp_all only [map_sub]
}

lemma expand_squared_term_nd {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((gradient I x) - ρ • (gradient B x ) )‖^2 =
    ∫ x in Ω, ‖(gradient I x)‖^2 - 2 • ρ • (∑ i, (gradient I x i) * (gradient B x i)) + (ρ^2) • ‖(gradient B x)‖^2

:= by
{

    let f := λ x ↦ (I x)
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (gradient B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        gradient (λ x ↦ I x - ρ • B x) x = gradient I x - ρ • gradient B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd_euclidean I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd_euclidean B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change gradient (λ x => f x - g x) a = (λ x ↦ (gradient f x ) - ρ • (gradient B x) ) a

        change gradient (λ x => f x - g x) a = (λ x ↦ (gradient f x ) - (gg x) ) a

        have ρBh : (gradient g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            simp only [← smul_eq_mul]
            simp only [(grad_const_mul B ρ a hB')]
        }
        simp only [←ρBh]

        change gradient (f - g ) a = (gradient f a) - (gradient g a)

        apply (grad_f_sub_g f g a hf' hg')
    }

    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf


    let u := gradient I x
    let v := ρ • gradient B x

    have v_sq_h : ρ ^ 2 • ‖(gradient B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (gradient I x i) • (gradient B x i)) * 2 + ρ ^ 2 • ‖(gradient B x)‖ ^ 2
    rw [v_sq_h]

    have h_ρ_factor
        (ρ : ℝ)
        (u : EuclideanSpace ℝ (Fin n))
        (B : EuclideanSpace ℝ (Fin n) → ℝ)
        (x : EuclideanSpace ℝ (Fin n))
    :
        (inner_prod_2ab_term_euclidean ρ u B x) = (∑ i, (u i) • ρ • (gradient B x i))
    := by
    {
        unfold inner_prod_2ab_term_euclidean

        rw [Finset.smul_sum]

        change ∑ (x_1 : Fin n), ρ • (u x_1) • ((gradient B x) x_1) = ∑ x_1, (u x_1) • ρ • ((gradient B x) x_1)

        let c (x_1 : Fin n ) := ((gradient B x) x_1 )

        change ∑ x_1, ρ • (u x_1) • (c x_1) = ∑ x_1, (u x_1) • ρ • (c x_1)

        let d (x_1 : Fin n ) := (u x_1)

        change ∑ x_1, ρ • (d x_1) • (c x_1) = ∑ x_1, (d x_1) • ρ • (c x_1)

        rw [Finset.sum_congr]
        rfl

        intro x h

        let d_ : ℝ := (d x)
        let c_ : ℝ := (c x)

        change ρ • d_ • c_ = d_ • ρ • c_
        rw [smul_comm]
    }


    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (u i) • (gradient B x i)) • 2 + ‖v‖ ^ 2
    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (inner_prod_2ab_term_euclidean ρ u B x) • 2 + ‖v‖ ^ 2

    rw [(h_ρ_factor ρ u B x)]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    have h_inner_prod_space : InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n) ) := by
    {
        refine
        {
            inner               := λ x y ↦ (∑ i, (x i) • (y i))
            norm_sq_eq_re_inner := by
            {
                intro x
                change ‖x‖ ^ 2 = RCLike.re (∑ i, (x i) • (x i))

                rw [pow_two]

                change ‖x‖ * ‖x‖ = RCLike.re (∑ i, (x i) • (x i))
                --simp only [Norm.norm]
                trace_state
            }
            conj_inner_symm     := by
            {
                intro x y
                simp only [starRingEnd_apply]

                have hstar : ∀ r : ℝ, star r = r := by intro r; simp only [star_trivial]

                rw [hstar]
                simp [mul_comm]
            }
            add_left            := by
            {
                intro x y z
                simp only [smul_eq_mul]

                simp_all only [smul_eq_mul, ae_restrict_eq, v]

                change ∑ x_1, ((x x_1) + (y x_1)) * (z x_1) = ∑ x_1, (x x_1) * (z x_1) + ∑ x_1, (y x_1) * (z x_1)

                have h_mul :
                  ∀ i,
                    ((x i) + (y i)) * (z i)
                      =
                    (x i) * (z i)
                      +
                    (y i) * (z i)
                := by
                {
                    intro i
                    ring
                }

                simp [h_mul, Finset.sum_add_distrib]
            }
            smul_left           := by
            {
                intro x y r
                have hstar : (starRingEnd ℝ) r = r := by simp only [conj_trivial]

                -- Rewrite `(r • x) v = r * x v`
                simp only [smul_eq_mul, hstar, Finset.mul_sum]
                trace_state
                --simp only [mul_assoc]
                sorry
            }

        }
    }


    change ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    trace_state

    rw [(norm_sub_sq_real) ]

    trace_state

    change ‖u‖ ^ 2 - 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    simp only [smul_eq_mul, add_left_inj, sub_right_inj]



    rw [←mul_right_inj' (by norm_num : (1/2 : ℝ) ≠ 0)]
    ring

    unfold inner
    trace_state



}

--------------------------------------------------------------------------------


import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Mathlib.Analysis.Normed.Operator.LinearIsometry

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace
open scoped BigOperators


def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}



noncomputable def inner_prod_2ab_term_euclidean
    {n : ℕ}
    (ρ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) )
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    (ρ • ∑ i, (u i) • (gradient B x i) )


lemma f_differentiable_within_nd_euclidean {n : ℕ }
  (I : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd_euclidean {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ


lemma grad_const_mul
    {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hB :  DifferentiableAt ℝ B a)
:
    gradient (fun x => ρ • B x) a = ρ • (gradient B a)
:= by
{
    simp only [gradient]

    let f := λ x ↦ (B x)
    have hf :  DifferentiableAt ℝ f a := by
    {
        unfold f
        fun_prop
    }

    change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (fun x => ρ • (f x)) a) =
  ρ • (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f a)

    have hhf : (fderiv ℝ (fun x => ρ • (f x)) a) = ρ • (fderiv ℝ f a) := by
    {
        rw [← (fderiv_const_smul hf ρ)]
        rfl
    }

    simp only [hhf]
    simp_all only [smul_eq_mul, map_smul, f]
}

lemma grad_f_sub_g
    {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hf :  DifferentiableAt ℝ f a)
    (hg :  DifferentiableAt ℝ g a)
:
    gradient (f - g) a = gradient f a - gradient g a
:= by
{
    simp only [gradient]
    rw [fderiv_sub hf hg]
    simp_all only [map_sub]
}

lemma expand_squared_term_nd {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((gradient I x) - ρ • (gradient B x ) )‖^2 =
    ∫ x in Ω, ‖(gradient I x)‖^2 - 2 • ρ • (∑ i, (gradient I x i) * (gradient B x i)) + (ρ^2) • ‖(gradient B x)‖^2

:= by
{

    let f := λ x ↦ (I x)
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (gradient B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        gradient (λ x ↦ I x - ρ • B x) x = gradient I x - ρ • gradient B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd_euclidean I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd_euclidean B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change gradient (λ x => f x - g x) a = (λ x ↦ (gradient f x ) - ρ • (gradient B x) ) a

        change gradient (λ x => f x - g x) a = (λ x ↦ (gradient f x ) - (gg x) ) a

        have ρBh : (gradient g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            simp only [← smul_eq_mul]
            simp only [(grad_const_mul B ρ a hB')]
        }
        simp only [←ρBh]

        change gradient (f - g ) a = (gradient f a) - (gradient g a)

        apply (grad_f_sub_g f g a hf' hg')
    }

    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf


    let u := gradient I x
    let v := ρ • gradient B x

    have v_sq_h : ρ ^ 2 • ‖(gradient B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (gradient I x i) • (gradient B x i)) * 2 + ρ ^ 2 • ‖(gradient B x)‖ ^ 2
    rw [v_sq_h]

    have h_ρ_factor
        (ρ : ℝ)
        (u : EuclideanSpace ℝ (Fin n))
        (B : EuclideanSpace ℝ (Fin n) → ℝ)
        (x : EuclideanSpace ℝ (Fin n))
    :
        (inner_prod_2ab_term_euclidean ρ u B x) = (∑ i, (u i) • ρ • (gradient B x i))
    := by
    {
        unfold inner_prod_2ab_term_euclidean

        rw [Finset.smul_sum]

        change ∑ (x_1 : Fin n), ρ • (u x_1) • ((gradient B x) x_1) = ∑ x_1, (u x_1) • ρ • ((gradient B x) x_1)

        let c (x_1 : Fin n ) := ((gradient B x) x_1 )

        change ∑ x_1, ρ • (u x_1) • (c x_1) = ∑ x_1, (u x_1) • ρ • (c x_1)

        let d (x_1 : Fin n ) := (u x_1)

        change ∑ x_1, ρ • (d x_1) • (c x_1) = ∑ x_1, (d x_1) • ρ • (c x_1)

        rw [Finset.sum_congr]
        rfl

        intro x h

        let d_ : ℝ := (d x)
        let c_ : ℝ := (c x)

        change ρ • d_ • c_ = d_ • ρ • c_
        rw [smul_comm]
    }


    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (u i) • (gradient B x i)) • 2 + ‖v‖ ^ 2
    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (inner_prod_2ab_term_euclidean ρ u B x) • 2 + ‖v‖ ^ 2

    rw [(h_ρ_factor ρ u B x)]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    have h_inner_prod_space : InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n) ) := by
    {
        refine
        {
            inner               := λ x y ↦ (∑ i, (x i) • (y i))
            norm_sq_eq_re_inner := by
            {
                intro x
                simp_all only
                [
                    smul_eq_mul,
                    ae_restrict_eq,
                    map_sum,
                    RCLike.mul_re,
                    RCLike.re_to_real,
                    RCLike.im_to_real,
                    mul_zero,
                    sub_zero,
                    v
                ]
                rw [@PiLp.norm_sq_eq_of_L2]
                change  ∑ i, ‖x.ofLp i‖ ^ 2 = ∑ i, x.ofLp i * x.ofLp i
                apply Finset.sum_congr
                rfl
                intro i hi
                simp only [norm_eq_abs, sq_abs]
                simp_all only [Finset.mem_univ]
                set a := x.ofLp i with ha
                rw [pow_two]
            }
            conj_inner_symm     := by
            {
                intro x y
                simp only [starRingEnd_apply]

                have hstar : ∀ r : ℝ, star r = r := by intro r; simp only [star_trivial]

                rw [hstar]
                simp [mul_comm]
            }
            add_left            := by
            {
                intro x y z
                simp only [smul_eq_mul]

                simp_all only [smul_eq_mul, ae_restrict_eq, v]

                change ∑ x_1, ((x x_1) + (y x_1)) * (z x_1) = ∑ x_1, (x x_1) * (z x_1) + ∑ x_1, (y x_1) * (z x_1)

                have h_mul :
                  ∀ i,
                    ((x i) + (y i)) * (z i)
                      =
                    (x i) * (z i)
                      +
                    (y i) * (z i)
                := by
                {
                    intro i
                    ring
                }

                simp [h_mul, Finset.sum_add_distrib]
            }
            smul_left           := by
            {
                intro x y r
                have hstar : (starRingEnd ℝ) r = r := by simp only [conj_trivial]

                -- Rewrite `(r • x) v = r * x v`
                simp only [smul_eq_mul, hstar, Finset.mul_sum]
                trace_state
                --simp only [mul_assoc]
                sorry
            }

        }
    }


    change ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    trace_state

    rw [(norm_sub_sq_real) ]

    trace_state

    change ‖u‖ ^ 2 - 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    simp only [smul_eq_mul, add_left_inj, sub_right_inj]



    rw [←mul_right_inj' (by norm_num : (1/2 : ℝ) ≠ 0)]
    ring_nf

    unfold inner
    trace_state



}

--------------------------------------------------------------------------------


import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Mathlib.Analysis.Normed.Operator.LinearIsometry

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace
open scoped BigOperators


def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}



noncomputable def inner_prod_2ab_term_euclidean
    {n : ℕ}
    (ρ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) )
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    (ρ • ∑ i, (u i) • (gradient B x i) )


lemma f_differentiable_within_nd_euclidean {n : ℕ }
  (I : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd_euclidean {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ


lemma grad_const_mul
    {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hB :  DifferentiableAt ℝ B a)
:
    gradient (fun x => ρ • B x) a = ρ • (gradient B a)
:= by
{
    simp only [gradient]

    let f := λ x ↦ (B x)
    have hf :  DifferentiableAt ℝ f a := by
    {
        unfold f
        fun_prop
    }

    change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (fun x => ρ • (f x)) a) =
  ρ • (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f a)

    have hhf : (fderiv ℝ (fun x => ρ • (f x)) a) = ρ • (fderiv ℝ f a) := by
    {
        rw [← (fderiv_const_smul hf ρ)]
        rfl
    }

    simp only [hhf]
    simp_all only [smul_eq_mul, map_smul, f]
}

lemma grad_f_sub_g
    {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hf :  DifferentiableAt ℝ f a)
    (hg :  DifferentiableAt ℝ g a)
:
    gradient (f - g) a = gradient f a - gradient g a
:= by
{
    simp only [gradient]
    rw [fderiv_sub hf hg]
    simp_all only [map_sub]
}

lemma expand_squared_term_nd {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((gradient I x) - ρ • (gradient B x ) )‖^2 =
    ∫ x in Ω, ‖(gradient I x)‖^2 - 2 • ρ • (∑ i, (gradient I x i) * (gradient B x i)) + (ρ^2) • ‖(gradient B x)‖^2

:= by
{

    let f := λ x ↦ (I x)
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (gradient B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        gradient (λ x ↦ I x - ρ • B x) x = gradient I x - ρ • gradient B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd_euclidean I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd_euclidean B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change gradient (λ x => f x - g x) a = (λ x ↦ (gradient f x ) - ρ • (gradient B x) ) a

        change gradient (λ x => f x - g x) a = (λ x ↦ (gradient f x ) - (gg x) ) a

        have ρBh : (gradient g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            simp only [← smul_eq_mul]
            simp only [(grad_const_mul B ρ a hB')]
        }
        simp only [←ρBh]

        change gradient (f - g ) a = (gradient f a) - (gradient g a)

        apply (grad_f_sub_g f g a hf' hg')
    }

    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf


    let u := gradient I x
    let v := ρ • gradient B x

    have v_sq_h : ρ ^ 2 • ‖(gradient B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (gradient I x i) • (gradient B x i)) * 2 + ρ ^ 2 • ‖(gradient B x)‖ ^ 2
    rw [v_sq_h]

    have h_ρ_factor
        (ρ : ℝ)
        (u : EuclideanSpace ℝ (Fin n))
        (B : EuclideanSpace ℝ (Fin n) → ℝ)
        (x : EuclideanSpace ℝ (Fin n))
    :
        (inner_prod_2ab_term_euclidean ρ u B x) = (∑ i, (u i) • ρ • (gradient B x i))
    := by
    {
        unfold inner_prod_2ab_term_euclidean

        rw [Finset.smul_sum]

        change ∑ (x_1 : Fin n), ρ • (u x_1) • ((gradient B x) x_1) = ∑ x_1, (u x_1) • ρ • ((gradient B x) x_1)

        let c (x_1 : Fin n ) := ((gradient B x) x_1 )

        change ∑ x_1, ρ • (u x_1) • (c x_1) = ∑ x_1, (u x_1) • ρ • (c x_1)

        let d (x_1 : Fin n ) := (u x_1)

        change ∑ x_1, ρ • (d x_1) • (c x_1) = ∑ x_1, (d x_1) • ρ • (c x_1)

        rw [Finset.sum_congr]
        rfl

        intro x h

        let d_ : ℝ := (d x)
        let c_ : ℝ := (c x)

        change ρ • d_ • c_ = d_ • ρ • c_
        rw [smul_comm]
    }


    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (u i) • (gradient B x i)) • 2 + ‖v‖ ^ 2
    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (inner_prod_2ab_term_euclidean ρ u B x) • 2 + ‖v‖ ^ 2

    rw [(h_ρ_factor ρ u B x)]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    have h_inner_prod_space : InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n) ) := by
    {
        refine
        {
            inner               := λ x y ↦ (∑ i, (x i) • (y i))
            norm_sq_eq_re_inner := by
            {
                intro x
                simp_all only
                [
                    smul_eq_mul,
                    ae_restrict_eq,
                    map_sum,
                    RCLike.mul_re,
                    RCLike.re_to_real,
                    RCLike.im_to_real,
                    mul_zero,
                    sub_zero,
                    v
                ]
                rw [@PiLp.norm_sq_eq_of_L2]
                change  ∑ i, ‖x.ofLp i‖ ^ 2 = ∑ i, x.ofLp i * x.ofLp i
                apply Finset.sum_congr
                rfl
                intro i hi
                simp only [norm_eq_abs, sq_abs]
                simp_all only [Finset.mem_univ]
                set a := x.ofLp i with ha
                rw [pow_two]
            }
            conj_inner_symm     := by
            {
                intro x y
                simp only [starRingEnd_apply]

                have hstar : ∀ r : ℝ, star r = r := by intro r; simp only [star_trivial]

                rw [hstar]
                simp [mul_comm]
            }
            add_left            := by
            {
                intro x y z
                simp only [smul_eq_mul]

                simp_all only [smul_eq_mul, ae_restrict_eq, v]

                change ∑ x_1, ((x x_1) + (y x_1)) * (z x_1) = ∑ x_1, (x x_1) * (z x_1) + ∑ x_1, (y x_1) * (z x_1)

                have h_mul :
                  ∀ i,
                    ((x i) + (y i)) * (z i)
                      =
                    (x i) * (z i)
                      +
                    (y i) * (z i)
                := by
                {
                    intro i
                    ring
                }

                simp [h_mul, Finset.sum_add_distrib]
            }
            smul_left           := by
            {
                trace_state
                intro x y r
                have hstar : (starRingEnd ℝ) r = r := by simp only [conj_trivial]

                -- Rewrite `(r • x) v = r * x v`
                simp only [smul_eq_mul, hstar, Finset.mul_sum]
                trace_state
                simp only [PiLp.smul_apply, smul_eq_mul]
                apply Finset.sum_congr
                rfl
                intro i hi
                rw [mul_assoc]
            }

        }
    }


    change ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    trace_state

    rw [(norm_sub_sq_real) ]

    trace_state

    change ‖u‖ ^ 2 - 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    simp only [smul_eq_mul, add_left_inj, sub_right_inj]



    rw [←mul_right_inj' (by norm_num : (1/2 : ℝ) ≠ 0)]
    ring_nf

    unfold inner
    trace_state



}


-------------------------------------------------------------------------------

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Mathlib.Analysis.Normed.Operator.LinearIsometry

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace
open scoped BigOperators


def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}



noncomputable def inner_prod_2ab_term_euclidean
    {n : ℕ}
    (ρ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) )
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    (ρ • ∑ i, (u i) • (gradient B x i) )


lemma f_differentiable_within_nd_euclidean {n : ℕ }
  (I : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd_euclidean {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ


lemma grad_const_mul
    {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hB :  DifferentiableAt ℝ B a)
:
    gradient (fun x => ρ • B x) a = ρ • (gradient B a)
:= by
{
    simp only [gradient]

    let f := λ x ↦ (B x)
    have hf :  DifferentiableAt ℝ f a := by
    {
        unfold f
        fun_prop
    }

    change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (fun x => ρ • (f x)) a) =
  ρ • (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f a)

    have hhf : (fderiv ℝ (fun x => ρ • (f x)) a) = ρ • (fderiv ℝ f a) := by
    {
        rw [← (fderiv_const_smul hf ρ)]
        rfl
    }

    simp only [hhf]
    simp_all only [smul_eq_mul, map_smul, f]
}

lemma grad_f_sub_g
    {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hf :  DifferentiableAt ℝ f a)
    (hg :  DifferentiableAt ℝ g a)
:
    gradient (f - g) a = gradient f a - gradient g a
:= by
{
    simp only [gradient]
    rw [fderiv_sub hf hg]
    simp_all only [map_sub]
}

lemma expand_squared_term_nd {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((gradient I x) - ρ • (gradient B x ) )‖^2 =
    ∫ x in Ω, ‖(gradient I x)‖^2 - 2 • ρ • (∑ i, (gradient I x i) * (gradient B x i)) + (ρ^2) • ‖(gradient B x)‖^2

:= by
{

    let f := λ x ↦ (I x)
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (gradient B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        gradient (λ x ↦ I x - ρ • B x) x = gradient I x - ρ • gradient B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd_euclidean I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd_euclidean B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change gradient (λ x => f x - g x) a = (λ x ↦ (gradient f x ) - ρ • (gradient B x) ) a

        change gradient (λ x => f x - g x) a = (λ x ↦ (gradient f x ) - (gg x) ) a

        have ρBh : (gradient g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            simp only [← smul_eq_mul]
            simp only [(grad_const_mul B ρ a hB')]
        }
        simp only [←ρBh]

        change gradient (f - g ) a = (gradient f a) - (gradient g a)

        apply (grad_f_sub_g f g a hf' hg')
    }

    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf


    let u := gradient I x
    let v := ρ • gradient B x

    have v_sq_h : ρ ^ 2 • ‖(gradient B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (gradient I x i) • (gradient B x i)) * 2 + ρ ^ 2 • ‖(gradient B x)‖ ^ 2
    rw [v_sq_h]

    have h_ρ_factor
        (ρ : ℝ)
        (u : EuclideanSpace ℝ (Fin n))
        (B : EuclideanSpace ℝ (Fin n) → ℝ)
        (x : EuclideanSpace ℝ (Fin n))
    :
        (inner_prod_2ab_term_euclidean ρ u B x) = (∑ i, (u i) • ρ • (gradient B x i))
    := by
    {
        unfold inner_prod_2ab_term_euclidean

        rw [Finset.smul_sum]

        change ∑ (x_1 : Fin n), ρ • (u x_1) • ((gradient B x) x_1) = ∑ x_1, (u x_1) • ρ • ((gradient B x) x_1)

        let c (x_1 : Fin n ) := ((gradient B x) x_1 )

        change ∑ x_1, ρ • (u x_1) • (c x_1) = ∑ x_1, (u x_1) • ρ • (c x_1)

        let d (x_1 : Fin n ) := (u x_1)

        change ∑ x_1, ρ • (d x_1) • (c x_1) = ∑ x_1, (d x_1) • ρ • (c x_1)

        rw [Finset.sum_congr]
        rfl

        intro x h

        let d_ : ℝ := (d x)
        let c_ : ℝ := (c x)

        change ρ • d_ • c_ = d_ • ρ • c_
        rw [smul_comm]
    }


    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (u i) • (gradient B x i)) • 2 + ‖v‖ ^ 2
    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (inner_prod_2ab_term_euclidean ρ u B x) • 2 + ‖v‖ ^ 2

    rw [(h_ρ_factor ρ u B x)]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    rw [(norm_sub_sq_real) ]

    change ‖u‖ ^ 2 - 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, (u i) • (v i)) • 2 + ‖v‖ ^ 2

    simp only [smul_eq_mul, add_left_inj, sub_right_inj]

    rw [←mul_right_inj' (by norm_num : (1/2 : ℝ) ≠ 0)]
    ring_nf

    simp only [inner, RCLike.inner_apply, conj_trivial]

    simp only [mul_comm]
}

---------------------------------------------------------------------------------
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Mathlib.Analysis.Normed.Operator.LinearIsometry

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace
open scoped BigOperators

--def ∇ := gradient


def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}



noncomputable def inner_prod_2ab_term_euclidean
    {n : ℕ}
    (ρ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) )
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    ρ • ⟪u , (gradient B x) ⟫_ℝ


lemma f_differentiable_within_nd_euclidean {n : ℕ }
  (I : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd_euclidean {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ


lemma grad_const_mul
    {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hB :  DifferentiableAt ℝ B a)
:
    gradient (fun x => ρ • B x) a = ρ • (gradient B a)
:= by
{
    simp only [gradient]

    let f := λ x ↦ (B x)
    have hf :  DifferentiableAt ℝ f a := by
    {
        unfold f
        fun_prop
    }

    change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (fun x => ρ • (f x)) a) =
  ρ • (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f a)

    have hhf : (fderiv ℝ (fun x => ρ • (f x)) a) = ρ • (fderiv ℝ f a) := by
    {
        rw [← (fderiv_const_smul hf ρ)]
        rfl
    }

    simp only [hhf]
    simp_all only [smul_eq_mul, map_smul, f]
}

lemma grad_f_sub_g
    {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hf :  DifferentiableAt ℝ f a)
    (hg :  DifferentiableAt ℝ g a)
:
    gradient (f - g) a = gradient f a - gradient g a
:= by
{
    simp only [gradient]
    rw [fderiv_sub hf hg]
    simp_all only [map_sub]
}

lemma expand_squared_term_nd {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((gradient I x) - ρ • (gradient B x ) )‖^2 =
    ∫ x in Ω, ‖(gradient I x)‖^2 - 2 • ρ • ⟪(gradient I x ) , (gradient B x )⟫_ℝ + (ρ^2) • ‖(gradient B x)‖^2
:= by
{

    let f := λ x ↦ (I x)
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (gradient B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        gradient (λ x ↦ I x - ρ • B x) x = gradient I x - ρ • gradient B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd_euclidean I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd_euclidean B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change gradient (λ x => f x - g x) a = (λ x ↦ (gradient f x ) - ρ • (gradient B x) ) a

        change gradient (λ x => f x - g x) a = (λ x ↦ (gradient f x ) - (gg x) ) a

        have ρBh : (gradient g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            simp only [← smul_eq_mul]
            simp only [(grad_const_mul B ρ a hB')]
        }
        simp only [←ρBh]

        change gradient (f - g ) a = (gradient f a) - (gradient g a)

        apply (grad_f_sub_g f g a hf' hg')
    }

    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf


    let u := gradient I x
    let v := ρ • gradient B x

    have v_sq_h : ρ ^ 2 • ‖(gradient B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ⟪(gradient I x ) , (gradient B x )⟫_ℝ ) * 2 + ρ ^ 2 • ‖(gradient B x)‖ ^ 2
    rw [v_sq_h]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ⟪(gradient I x ) , (gradient B x )⟫_ℝ ) • 2 + ‖v‖ ^ 2

    have h_inner : (ρ • ⟪(gradient I x ) , (gradient B x )⟫_ℝ ) = ⟪u, v⟫_ℝ := by
    {
        unfold u v
        simp [inner_smul_right]
    }

    rw [h_inner]
    simp only [norm_sub_sq_real, smul_eq_mul, mul_comm]
}

-------------------------------------------------------------------------------

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace
open scoped BigOperators


notation "∇" => gradient


def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}


noncomputable def inner_prod_2ab_term_euclidean
    {n : ℕ}
    (ρ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) )
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    ρ • ⟪u , (∇ B x) ⟫_ℝ


lemma f_differentiable_within_nd_euclidean {n : ℕ }
  (I : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd_euclidean {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ


lemma grad_const_mul
    {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hB :  DifferentiableAt ℝ B a)
:
    ∇ (fun x => ρ • B x) a = ρ • (∇ B a)
:= by
{
    simp only [gradient]

    let f := λ x ↦ (B x)
    have hf :  DifferentiableAt ℝ f a := by
    {
        unfold f
        fun_prop
    }

    change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (fun x => ρ • (f x)) a) =
  ρ • (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f a)

    have hhf : (fderiv ℝ (fun x => ρ • (f x)) a) = ρ • (fderiv ℝ f a) := by
    {
        rw [← (fderiv_const_smul hf ρ)]
        rfl
    }

    simp only [hhf]
    simp_all only [smul_eq_mul, map_smul, f]
}

lemma grad_f_sub_g
    {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hf :  DifferentiableAt ℝ f a)
    (hg :  DifferentiableAt ℝ g a)
:
    ∇ (f - g) a = ∇ f a - ∇ g a
:= by
{
    simp only [gradient]
    rw [fderiv_sub hf hg]
    simp_all only [map_sub]
}

lemma expand_squared_term_nd {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((∇ I x) - ρ • (∇ B x ) )‖^2 =
    ∫ x in Ω, ‖(∇ I x)‖^2 - 2 • ρ • ⟪(∇ I x ) , (∇ B x )⟫_ℝ + (ρ^2) • ‖(∇ B x)‖^2
:= by
{

    let f := λ x ↦ (I x)
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (∇ B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        ∇ (λ x ↦ I x - ρ • B x) x = ∇ I x - ρ • ∇ B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd_euclidean I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd_euclidean B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change ∇ (λ x ↦ f x - g x) a = (λ x ↦ (∇ f x ) - ρ • (∇ B x) ) a

        change ∇ (λ x ↦ f x - g x) a = (λ x ↦ (∇ f x ) - (gg x) ) a

        have ρBh : (∇ g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            simp only [← smul_eq_mul]
            simp only [(grad_const_mul B ρ a hB')]
        }
        simp only [←ρBh]

        change ∇ (f - g ) a = (∇ f a) - (∇ g a)

        apply (grad_f_sub_g f g a hf' hg')
    }

    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf


    let u := ∇ I x
    let v := ρ • ∇ B x

    have v_sq_h : ρ ^ 2 • ‖(∇ B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ⟪(∇ I x ) , (∇ B x )⟫_ℝ ) * 2 + ρ ^ 2 • ‖(∇ B x)‖ ^ 2
    rw [v_sq_h]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ⟪(∇ I x ) , (∇ B x )⟫_ℝ ) • 2 + ‖v‖ ^ 2

    have h_inner : (ρ • ⟪(∇ I x ) , (∇ B x )⟫_ℝ ) = ⟪u, v⟫_ℝ := by
    {
        unfold u v
        simp [inner_smul_right]
    }

    rw [h_inner]
    simp only [norm_sub_sq_real, smul_eq_mul, mul_comm]
}

--------------------------------------------------------------------------------

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

import AdaptiveSubtraction.Quadratics

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace

open scoped BigOperators


notation "∇" => gradient


def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}


def image_and_background_are_edgable_ND
    {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω :  Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
: Prop :=
    let f := λ x ↦ ‖∇ I x‖^2
    let g := λ x ↦ ∑ i, (∇ I x) i * (∇ B x) i
    let h := λ x ↦ ‖∇ B x‖^2
    Integrable f (volume.restrict Ω) ∧ Integrable g (volume.restrict Ω) ∧ Integrable h (volume.restrict Ω)


noncomputable def edginess_ND {n}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (ρ : ℝ) : ℝ :=
  ∫ x in Ω, ‖∇ (λ x => I x - ρ • B x) x‖^2


noncomputable def ρ_opt_nd {n : ℕ}
  (I B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper :  EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
: ℝ :=
  ∫ x in Ω, (∑ i, (∇ I x) i * (∇ B x) i) / (∫ x in Ω, ‖∇ B x‖^2)


noncomputable def c_coef_nd {n : ℕ}
  (I : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper :  EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper)) : ℝ
    := (∫ x in Ω, (‖∇ I x‖) ^ 2)


noncomputable def b_coef_nd {n : ℕ}
  (I B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper :  EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper)) : ℝ
    := - 2 • ∫ x in Ω, ∑ i, (∇ I x) i * (∇ B x) i

noncomputable def a_coef_nd {n : ℕ}
  (B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper :  EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper)) : ℝ
    := ∫ x in Ω, ‖∇ B x‖ ^ 2


noncomputable def edginess_polynomial_ND {n : ℕ }
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (ρ : ℝ)
: ℝ :=
    (quadratic (a_coef_nd B lower upper Ω ) (b_coef_nd I B lower upper Ω ) (c_coef_nd I lower upper Ω) ρ )


lemma scalar_mul_differentiable_within_nd {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : Fin n → ℝ)
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ



lemma grad_const_mul
    {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hB :  DifferentiableAt ℝ B a)
:
    ∇ (fun x => ρ • B x) a = ρ • (∇ B a)
:= by
{
    simp only [gradient]

    let f := λ x ↦ (B x)
    have hf :  DifferentiableAt ℝ f a := by
    {
        unfold f
        fun_prop
    }

    change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (fun x => ρ • (f x)) a) =
  ρ • (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f a)

    have hhf : (fderiv ℝ (fun x => ρ • (f x)) a) = ρ • (fderiv ℝ f a) := by
    {
        rw [← (fderiv_const_smul hf ρ)]
        rfl
    }

    simp only [hhf]
    simp_all only [smul_eq_mul, map_smul, f]
}


lemma grad_f_sub_g
    {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hf :  DifferentiableAt ℝ f a)
    (hg :  DifferentiableAt ℝ g a)
:
    ∇ (f - g) a = ∇ f a - ∇ g a
:= by
{
    simp only [gradient]
    rw [fderiv_sub hf hg]
    simp_all only [map_sub]
}


lemma deriv_distributes_over_sub_within_integral_nd {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω  : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM : MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ  : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖∇ (λ x ↦ I x - ρ • B x) x‖^2 =
    ∫ x in Ω, ‖(λ x ↦ ∇ I x - ρ • ∇ B x) x‖^2
:= by
{
    let f := I
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (∇ B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        ∇ (λ x ↦ I x - ρ • B x) x = ∇ I x - ρ • ∇ B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change ∇ (λ x => f x - g x) a = (λ x ↦ (∇ f x ) - ρ • (∇ B x) ) a

        change ∇ (λ x => f x - g x) a = (λ x ↦ (∇ f x ) - (gg x) ) a

        have ρBh : (∇ g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [f, g]

            unfold gradient

            let R := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
            change R (fderiv ℝ (fun x ↦ ρ • B x) a) = ρ • R (fderiv ℝ B a)

            have hhf : (fderiv ℝ (fun x => ρ • (B x)) a) = ρ • (fderiv ℝ B a) := by
            {
                rw [← (fderiv_const_smul hB' ρ)]
                rfl
            }

            simp only [hhf]
            simp_all only [smul_eq_mul, differentiableAt_const, DifferentiableAt.fun_mul, map_smul, R]
        }
        simp only [←ρBh]
        change ∇ (f - g ) a = (∇ f a) - (∇ g a)

        apply (grad_f_sub_g f g a hf' hg')
    }

    filter_upwards [h_deriv_eq] with x hx
    simp only [hx]
}


lemma expand_squared_term_nd {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((∇ I x) - ρ • (∇ B x ) )‖^2 =
    ∫ x in Ω, ‖(∇ I x)‖^2 - 2 • ρ • ⟪(∇ I x ) , (∇ B x )⟫_ℝ + (ρ^2) • ‖(∇ B x)‖^2
:= by
{

    let f := λ x ↦ (I x)
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (∇ B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        ∇ (λ x ↦ I x - ρ • B x) x = ∇ I x - ρ • ∇ B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change ∇ (λ x ↦ f x - g x) a = (λ x ↦ (∇ f x ) - ρ • (∇ B x) ) a

        change ∇ (λ x ↦ f x - g x) a = (λ x ↦ (∇ f x ) - (gg x) ) a

        have ρBh : (∇ g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            simp only [← smul_eq_mul]
            simp only [(grad_const_mul B ρ a hB')]
        }
        simp only [←ρBh]

        change ∇ (f - g ) a = (∇ f a) - (∇ g a)

        apply (grad_f_sub_g f g a hf' hg')
    }

    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf


    let u := ∇ I x
    let v := ρ • ∇ B x

    have v_sq_h : ρ ^ 2 • ‖(∇ B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ⟪(∇ I x ) , (∇ B x )⟫_ℝ ) * 2 + ρ ^ 2 • ‖(∇ B x)‖ ^ 2
    rw [v_sq_h]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ⟪(∇ I x ) , (∇ B x )⟫_ℝ ) • 2 + ‖v‖ ^ 2

    have h_inner : (ρ • ⟪(∇ I x ) , (∇ B x )⟫_ℝ ) = ⟪u, v⟫_ℝ := by
    {
        unfold u v
        simp [inner_smul_right]
    }

    rw [h_inner]
    simp only [norm_sub_sq_real, smul_eq_mul, mul_comm]
}


lemma distribute_integral_fgh {n : ℕ }
    (f g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω :  Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hIf : Integrable f (volume.restrict Ω))
    (hIg : Integrable g (volume.restrict Ω))
    (hIh : Integrable h (volume.restrict Ω))
:
    ∫ x in Ω, (f x) - (g x) + (h x) = (∫ x in Ω, (f x)) - (∫ x in Ω, (g x)) + ∫ x in Ω, (h x)
:= by
{
    let ff := λ x ↦ (f x) - (g x)

    have hIff : Integrable ff (volume.restrict Ω) := by
    {
        dsimp [ff]
        exact hIf.sub hIg
    }

    change ∫ x in Ω, (ff x) + (h x) = (∫ x in Ω, (f x)) - (∫ x in Ω, (g x)) + ∫ x in Ω, (h x)

    rw [(integral_add hIff hIh)]

    unfold ff
    rw [(integral_sub hIf hIg)]
}


--def Rn { n: ℕ } := EuclideanSpace ℝ (Fin n)

noncomputable def I_Squared_Term{n:ℕ} (I : EuclideanSpace ℝ (Fin n) → ℝ)(x : EuclideanSpace ℝ (Fin n)) := ⟪ ∇ I x, ∇ I x ⟫_ℝ
noncomputable def IB_Term {n : ℕ} (I B : EuclideanSpace ℝ (Fin n) → ℝ)(x : EuclideanSpace ℝ (Fin n))(ρ : ℝ) := ρ * ⟪ ∇ I x, ∇ B x ⟫_ℝ * 2
noncomputable def B_Squared_Term{n : ℕ} (B : EuclideanSpace ℝ (Fin n) → ℝ)(x : EuclideanSpace ℝ (Fin n))(ρ : ℝ) := (ρ^2) * ⟪ ∇ B x, ∇ B x ⟫_ℝ

noncomputable def Int_I_Squared_Term{n : ℕ}
    (I : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
:=
    ∫ x in Ω, ⟪ ∇ I x, ∇ I x ⟫_ℝ

noncomputable def Int_IB_Term {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
:=
    (ρ * (2 * ∫ x in Ω, ⟪ ∇ I x, ∇ B x ⟫_ℝ ))

-----

noncomputable def Int_B_Squared_Term(B : ℝ → ℝ)(ρ : ℝ)(lower upper : ℝ)(Ω : Set ℝ := Set.Ioo lower upper) := (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2

noncomputable def Int_IB_Term_2(I B : ℝ → ℝ)(ρ : ℝ)(lower upper : ℝ)(Ω : Set ℝ := Set.Ioo lower upper) := (ρ * ∫ (x : ℝ) in Ω, deriv I x * deriv B x) * 2


--------------------------------------------------------------------------------------------------
