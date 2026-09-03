import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_comap_adjoin_singleton_eq_bot_of_mem_minimalPrimes_of_flat_of_isIntegral

set_option autoImplicit false
open scoped TensorProduct

theorem Ideal.comap_adjoin_singleton_eq_bot_of_mem_minimalPrimes_of_flat_of_isIntegral
    (A : Type) [CommRing A] [IsDomain A] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L]
    (B : Type) [CommRing B] [Algebra A B] [Module.Flat A B] (x : B)
    (hint : Algebra.IsIntegral ↥(Algebra.adjoin A ({x} : Set B)) B)
    (hni : ∀ 𝔓 ∈ (⊥ : Ideal (L ⊗[A] B)).minimalPrimes, ¬ 𝔓.IsMaximal) :
    ∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes,
      Ideal.comap (algebraMap ↥(Algebra.adjoin A ({x} : Set B)) B) 𝔭 = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_Ideal_comap_adjoin_singleton_eq_bot_of_mem_minimalPrimes_of_flat_of_isIntegral.solution
