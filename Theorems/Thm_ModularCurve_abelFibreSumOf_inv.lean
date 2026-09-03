import Mathlib
import Definitions.Def_ModularCurve_AbelFibreSumOf
import P2M.Util
import P2M.Sol.S_ModularCurve_abelFibreSumOf_inv

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.abelFibreSumOf_inv
    (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ) {t : ℂ} (ht : t ≠ 0) :
    ModularCurve.abelFibreSumOf Γ (fun τ : ℍ => (F τ)⁻¹) t⁻¹ =
      ModularCurve.abelFibreSumOf Γ F t := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_abelFibreSumOf_inv.solution
