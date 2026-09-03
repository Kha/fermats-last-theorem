import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import P2M.Util
import P2M.Sol.S_IsIntegral_mem_span_of_adjoin_simple_constants_transcendental

set_option autoImplicit false

theorem IsIntegral.mem_span_of_adjoin_simple_constants_transcendental {K : Type*}
    [Field K] [Algebra ℂ K]
    (F : IntermediateField ℚ ℂ) (t : K) (ht : Transcendental ℂ t)
    (S : Set K) (htS : t ∈ S) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral
      ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ {t})) s)
    (c : ℂ) (hc : Transcendental ↥F c)
    (htc : Transcendental ↥(Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S))
      (algebraMap ℂ K c))
    (y : K)
    (hyS : y ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    (hyB : IsIntegral ↥(Subring.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ {t})) y) :
    y ∈ Submodule.span ℂ {z : K | z ∈ Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) ∧
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ {t})) z} := by p2m_exact_reverting @_root_.P2MW.S_IsIntegral_mem_span_of_adjoin_simple_constants_transcendental.solution
