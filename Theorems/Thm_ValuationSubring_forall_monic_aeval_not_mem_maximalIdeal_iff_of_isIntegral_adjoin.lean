import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_forall_monic_aeval_not_mem_maximalIdeal_iff_of_isIntegral_adjoin

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.forall_monic_aeval_not_mem_maximalIdeal_iff_of_isIntegral_adjoin
    (A K : Type) [CommRing A] [IsLocalRing A] [Field K] [Algebra A K] (V : ValuationSubring K)
    (hAV : ∀ a : A, algebraMap A K a ∈ V)
    (hmV : ∀ a : A, a ∈ maximalIdeal A → (⟨algebraMap A K a, hAV a⟩ : ↥V) ∈ maximalIdeal ↥V)
    (x y : K) (hx : x ∈ V) (hy : y ∈ V)
    (hxy : IsIntegral ↥(Algebra.adjoin A ({x} : Set K)) y)
    (hyx : IsIntegral ↥(Algebra.adjoin A ({y} : Set K)) x) :
    (∀ p : Polynomial A, p.Monic → ∀ hp : Polynomial.aeval x (p.map (algebraMap A K)) ∈ V,
        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) ↔
    (∀ p : Polynomial A, p.Monic → ∀ hp : Polynomial.aeval y (p.map (algebraMap A K)) ∈ V,
        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_forall_monic_aeval_not_mem_maximalIdeal_iff_of_isIntegral_adjoin.solution
