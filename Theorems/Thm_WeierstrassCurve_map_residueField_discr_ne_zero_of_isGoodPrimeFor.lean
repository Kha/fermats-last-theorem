import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_map_residueField_discr_ne_zero_of_isGoodPrimeFor

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.map_residueField_discr_ne_zero_of_isGoodPrimeFor (W : WeierstrassCurve ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hgood : W.IsGoodPrimeFor ℓ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) : (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).Δ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_map_residueField_discr_ne_zero_of_isGoodPrimeFor.solution
