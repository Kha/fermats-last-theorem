import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_map_eq_and_isGamma0PowAt_of_isGamma0PowAt_map

set_option autoImplicit false

universe u

open Polynomial

theorem ModularCurve.exists_map_eq_and_isGamma0PowAt_of_isGamma0PowAt_map
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀) (p k : ℕ) (hp : IsUnit ((p : ℕ) : R₀))
    (h' : Polynomial K) (hh' : ModularCurve.IsGamma0PowAt (W₀.map (algebraMap R₀ K)) p k h') :
    ∃ h₀ : Polynomial R₀, h₀.map (algebraMap R₀ K) = h' ∧ ModularCurve.IsGamma0PowAt W₀ p k h₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_map_eq_and_isGamma0PowAt_of_isGamma0PowAt_map.solution
