import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import P2M.Util
import P2M.Sol.S_IsIntegral_mem_span_of_adjoin_simple_constants

theorem IsIntegral.mem_span_of_adjoin_simple_constants {K : Type*} [Field K] [Algebra ℂ K]
    (F : IntermediateField ℚ ℂ) (B S : Set K) (hBS : B ⊆ S) (c : ℂ) (hc : IsAlgebraic ↥F c)
    (y : K)
    (hyS : y ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    (hyB : IsIntegral ↥(Subring.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ B)) y) :
    y ∈ Submodule.span ℂ {z : K | z ∈ Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) ∧
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ B)) z} := by p2m_exact_reverting @_root_.P2MW.S_IsIntegral_mem_span_of_adjoin_simple_constants.solution
