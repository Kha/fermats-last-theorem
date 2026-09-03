import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_mem_minimalPrimes_map_maximalIdeal_of_not_isMaximal_of_fg_of_isAlgebraic_adjoin

set_option autoImplicit false

theorem Subalgebra.mem_minimalPrimes_map_maximalIdeal_of_not_isMaximal_of_fg_of_isAlgebraic_adjoin
    {A₀ : Type} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    {F : Type} [Field F] [Algebra A₀ F]
    (B : Subalgebra A₀ F) (hBfg : B.FG)

    (t : F) (halg : ∀ x : F, IsAlgebraic ↥(Algebra.adjoin A₀ ({t} : Set F)) x)
    (𝔮 : Ideal ↥B) (h𝔮 : 𝔮.IsPrime)
    (hle : Ideal.map (algebraMap A₀ ↥B) (IsLocalRing.maximalIdeal A₀) ≤ 𝔮) (hmax : ¬ 𝔮.IsMaximal) :
    𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (IsLocalRing.maximalIdeal A₀)).minimalPrimes := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_mem_minimalPrimes_map_maximalIdeal_of_not_isMaximal_of_fg_of_isAlgebraic_adjoin.solution
