import Theorems.Thm_MeasureTheory_L2_exists_convolutionCLM_isCompactOperator
import Theorems.Thm_MeasureTheory_L2_convolutionCLM_isSymmetric_of_conj_neg
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Operator.Mul
import P2M.Util
namespace P2MW.S_MeasureTheory_L2_exists_convolutionCLM_isCompactOperator_of_compactSpace
attribute [-simp] MeasureTheory.L2.kernelIntegralLM_apply

open scoped Convolution
open MeasureTheory
set_option autoImplicit false

theorem solution
    (G : Type*) [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure] [MeasureTheory.IsFiniteMeasure μ]
    (f : C(G, ℂ)) (hf : ∀ x, f (-x) = star (f x)) :
    ∃ T : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ,
      (∀ φ : MeasureTheory.Lp ℂ 2 μ, (T φ : G → ℂ) =ᵐ[μ]
        ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : G → ℂ))) ∧
      IsCompactOperator T ∧
      LinearMap.IsSymmetric (T : MeasureTheory.Lp ℂ 2 μ →ₗ[ℂ] MeasureTheory.Lp ℂ 2 μ) := by
  obtain ⟨T, hT_conv, hT_compact⟩ :=
    MeasureTheory.L2.exists_convolutionCLM_isCompactOperator G μ f
  exact ⟨T, hT_conv, hT_compact,
    MeasureTheory.L2.convolutionCLM_isSymmetric_of_conj_neg G μ f hf T hT_conv⟩
