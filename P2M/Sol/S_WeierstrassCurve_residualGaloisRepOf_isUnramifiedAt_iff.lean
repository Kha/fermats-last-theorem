import Definitions.Def_GaloisRep_Residual
import P2M.Util
namespace P2MW.S_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_iff

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p))
    (q : ℕ) :
    (W.residualGaloisRepOf p hcard hker).IsUnramifiedAt q ↔
      WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ W p q := by
  refine forall_congr' fun A => forall_congr' fun _ => forall_congr' fun σ => forall_congr' fun _ => ?_
  constructor
  · intro h x
    have hx := LinearMap.congr_fun h x
    simp at hx
    exact hx
  · intro h
    exact LinearMap.ext fun x => by have h__af := h x; simp at h__af ⊢; exact h__af
