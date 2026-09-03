import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq
    {k : Type*} [Field k] [DecidableEq k] (X Y : WeierstrassCurve k) (C : WeierstrassCurve.VariableChange k)
    (hC : C • X = Y) :
    ∃ φ : ↥(WeierstrassCurve.rationalEndSubring k X) ≃+* ↥(WeierstrassCurve.rationalEndSubring k Y),
      ∀ (α : ↥(WeierstrassCurve.rationalEndSubring k X)) (P : (Y⁄k).Point),
        ((φ α : ↥(WeierstrassCurve.rationalEndSubring k Y)) : AddMonoid.End (Y⁄k).Point) P =
          (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hC).symm
            ((α : AddMonoid.End (X⁄k).Point) (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hC P)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.solution
