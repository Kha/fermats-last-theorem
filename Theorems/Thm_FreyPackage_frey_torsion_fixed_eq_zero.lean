import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_FreyPackage_frey_torsion_fixed_eq_zero

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem FreyPackage.frey_torsion_fixed_eq_zero (P : FreyPackage) (x : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) (hx : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), σ • x = x) : x = 0 := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_frey_torsion_fixed_eq_zero.solution
