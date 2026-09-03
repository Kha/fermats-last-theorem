import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul
    {X : Scheme.{u}} {M : X.Modules} {V : X.Opens} {d : ℕ} (f f' : Fin d → Γ(M, V))
    (a : Matrix (Fin d) (Fin d) Γ(X, V)) (h : ∀ j, f' j = ∑ i, a i j • f i) :
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower X d).obj M.val)).app (op V)
      (show ((Scheme.Modules.presheafExteriorPower X d).obj M.val).obj (op V) from exteriorPower.ιMulti Γ(X, V) d f') :
      Γ(Scheme.Modules.det d M, V)) =
    a.det • (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower X d).obj M.val)).app (op V)
      (show ((Scheme.Modules.presheafExteriorPower X d).obj M.val).obj (op V) from exteriorPower.ιMulti Γ(X, V) d f) :
      Γ(Scheme.Modules.det d M, V)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul.solution
