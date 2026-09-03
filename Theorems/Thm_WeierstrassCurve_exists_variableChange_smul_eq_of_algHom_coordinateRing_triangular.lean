import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_smul_eq_of_algHom_coordinateRing_triangular

set_option autoImplicit false

open Polynomial

theorem WeierstrassCurve.exists_variableChange_smul_eq_of_algHom_coordinateRing_triangular
    (T : Type) [CommRing T] (W W' : WeierstrassCurve T)
    (g : W.toAffine.CoordinateRing →ₐ[T] W'.toAffine.CoordinateRing)
    (v₁ v₂ : Tˣ) (r s' t : T)
    (hx : g (WeierstrassCurve.Affine.CoordinateRing.mk W (C X)) =
      (v₁ : T) • WeierstrassCurve.Affine.CoordinateRing.mk W' (C X) + algebraMap T _ r)
    (hy : g (WeierstrassCurve.Affine.CoordinateRing.mk W X) =
      (v₂ : T) • WeierstrassCurve.Affine.CoordinateRing.mk W' X +
        s' • WeierstrassCurve.Affine.CoordinateRing.mk W' (C X) + algebraMap T _ t) :
    ∃ C : WeierstrassCurve.VariableChange T,
      C • W = W' ∧ ((C.u : T) ^ 2 = v₁ ∧ (C.u : T) ^ 3 = v₂) ∧ C.r = r ∧ (C.u : T) ^ 2 * C.s = s' ∧ C.t = t := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_of_algHom_coordinateRing_triangular.solution
