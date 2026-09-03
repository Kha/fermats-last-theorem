import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_map_eq_and_isGamma0PowAt_tuple_of_isGamma0PowAt_map

set_option autoImplicit false

universe u

open Polynomial

theorem ModularCurve.exists_map_eq_and_isGamma0PowAt_tuple_of_isGamma0PowAt_map
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀) (M' : ℕ) (hM' : IsUnit ((M' : ℕ) : R₀))
    (hh' : ↥M'.primeFactors → Polynomial K)
    (H' : ∀ p : ↥M'.primeFactors,
      ModularCurve.IsGamma0PowAt (W₀.map (algebraMap R₀ K)) (p : ℕ) (M'.factorization (p : ℕ)) (hh' p)) :
    ∃ hh₀ : ↥M'.primeFactors → Polynomial R₀,
      (fun p => (hh₀ p).map (algebraMap R₀ K)) = hh' ∧
      ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W₀ (p : ℕ) (M'.factorization (p : ℕ)) (hh₀ p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_map_eq_and_isGamma0PowAt_tuple_of_isGamma0PowAt_map.solution
