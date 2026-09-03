import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_aeval_notMem_of_mem_minimalPrimes_span_natCast

open ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.aeval_notMem_of_mem_minimalPrimes_span_natCast
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (y : ↥(modularFunctionFieldFull N)) (hy : Transcendental ℚ y)
    (𝔭 : Ideal ↥(chartAlg N ℓ ({y} : Set ↥(modularFunctionFieldFull N))))
    (h𝔭 : 𝔭 ∈ (Ideal.span
      {((ℓ : ℕ) : ↥(chartAlg N ℓ ({y} : Set ↥(modularFunctionFieldFull N))))}).minimalPrimes)
    (P : Polynomial ℤ) (hP : P.map (Int.castRingHom (ZMod ℓ)) ≠ 0) :
    Polynomial.aeval (⟨y, subset_chartAlg N ℓ _ (Set.mem_singleton y)⟩ :
        ↥(chartAlg N ℓ ({y} : Set ↥(modularFunctionFieldFull N)))) P ∉ 𝔭 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_aeval_notMem_of_mem_minimalPrimes_span_natCast.solution
