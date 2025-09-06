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
