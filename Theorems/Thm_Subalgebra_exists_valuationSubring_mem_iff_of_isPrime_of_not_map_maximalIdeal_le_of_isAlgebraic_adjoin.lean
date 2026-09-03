import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_exists_valuationSubring_mem_iff_of_isPrime_of_not_map_maximalIdeal_le_of_isAlgebraic_adjoin

set_option autoImplicit false

open IsLocalRing

theorem Subalgebra.exists_valuationSubring_mem_iff_of_isPrime_of_not_map_maximalIdeal_le_of_isAlgebraic_adjoin
    {A₀ : Type} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    {F : Type} [Field F] [Algebra A₀ F]
    (B : Subalgebra A₀ F) (hBfg : B.FG)
    (hBn : ∀ x : F, IsIntegral ↥B x → x ∈ B)
    (hBfrac : ∀ x : F, ∃ b c : F, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b)

    (t : F) (halg : ∀ x : F, IsAlgebraic ↥(Algebra.adjoin A₀ ({t} : Set F)) x)
    (𝔭 : Ideal ↥B) (h𝔭 : 𝔭.IsPrime) (h𝔭0 : 𝔭 ≠ ⊥)
    (hgen : ¬ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭)) :
    ∃ V : ValuationSubring F, ∀ f : F, f ∈ V ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F) = (b : F) := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_exists_valuationSubring_mem_iff_of_isPrime_of_not_map_maximalIdeal_le_of_isAlgebraic_adjoin.solution
