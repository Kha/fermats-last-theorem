import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_map_eq_and_isGamma1Point_of_isGamma1Point_map

set_option autoImplicit false

universe u

theorem ModularCurve.exists_map_eq_and_isGamma1Point_of_isGamma1Point_map
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀) (ℓ : ℕ) (hℓ : IsUnit ((ℓ : ℕ) : R₀))
    (D' : ModularCurve.LevelPData K) (hD' : ModularCurve.IsGamma1Point (W₀.map (algebraMap R₀ K)) ℓ D') :
    ∃ D₀ : ModularCurve.LevelPData R₀, D₀.map (algebraMap R₀ K) = D' ∧ ModularCurve.IsGamma1Point W₀ ℓ D₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_map_eq_and_isGamma1Point_of_isGamma1Point_map.solution
