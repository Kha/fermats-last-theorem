import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_iff_mem_of_mem_adjoin_simple_of_forall_aeval_inv_mem

set_option autoImplicit false

theorem ValuationSubring.mem_iff_mem_of_mem_adjoin_simple_of_forall_aeval_inv_mem
    (L : Type) [Field L] (A₀ : ValuationSubring L)
    (ϖ : ↥A₀) (hϖ : IsLocalRing.maximalIdeal ↥A₀ = Ideal.span {ϖ})
    (F : Type) [Field F] [Algebra L F] [Algebra ↥A₀ F] [IsScalarTower ↥A₀ L F]
    (x : F) (V V' : ValuationSubring F)
    (hV : ∀ r : ↥A₀, algebraMap ↥A₀ F r ∈ V) (hϖV : algebraMap ↥A₀ F ϖ ∈ V.nonunits)
    (hxV : ∀ P : Polynomial ↥A₀, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval x P ∈ V ∧ (Polynomial.aeval x P)⁻¹ ∈ V)
    (hV' : ∀ r : ↥A₀, algebraMap ↥A₀ F r ∈ V') (hϖV' : algebraMap ↥A₀ F ϖ ∈ V'.nonunits)
    (hxV' : ∀ P : Polynomial ↥A₀, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval x P ∈ V' ∧ (Polynomial.aeval x P)⁻¹ ∈ V') :
    ∀ e : F, e ∈ IntermediateField.adjoin L ({x} : Set F) → (e ∈ V ↔ e ∈ V') := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_iff_mem_of_mem_adjoin_simple_of_forall_aeval_inv_mem.solution
