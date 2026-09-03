import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_nonsingular_residue_of_isGoodPrimeFor

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.nonsingular_residue_of_isGoodPrimeFor (W : WeierstrassCurve ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hgood : W.IsGoodPrimeFor ℓ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) {x y : AlgebraicClosure ℚ} (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Equation x y) (hx : x ∈ A) (hy : y ∈ A) : (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.Nonsingular (IsLocalRing.residue A ⟨x, hx⟩) (IsLocalRing.residue A ⟨y, hy⟩) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_nonsingular_residue_of_isGoodPrimeFor.solution
