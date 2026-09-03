import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exteriorPower_map_app_unit_iotaMulti_eq_det_smul

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite
theorem AlgebraicGeometry.Scheme.Modules.exteriorPower_map_app_unit_iotaMulti_eq_det_smul
    {X : Scheme.{u}} {n : ℕ} {M N : X.Modules} (φ : M ⟶ N) {U : X.Opens}
    (e : Fin n → Γ(M, U)) (f : Fin n → Γ(N, U)) (a : Matrix (Fin n) (Fin n) Γ(X, U))
    (ha : ∀ j, φ.app U (e j) = ∑ i, a i j • f i) :
    ((Scheme.Modules.exteriorPower X n).map φ).app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower X n).obj M.val)).app (op U)
          (show ((Scheme.Modules.presheafExteriorPower X n).obj M.val).obj (op U) from
            exteriorPower.ιMulti Γ(X, U) n e)) =
      a.det • (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower X n).obj N.val)).app (op U)
          (show ((Scheme.Modules.presheafExteriorPower X n).obj N.val).obj (op U) from
            exteriorPower.ιMulti Γ(X, U) n f) : Γ(Scheme.Modules.det n N, U)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exteriorPower_map_app_unit_iotaMulti_eq_det_smul.solution
