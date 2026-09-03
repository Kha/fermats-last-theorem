import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exteriorPower_map_app_unit_iotaMulti_eq_det_smul
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite

theorem solution
    {X : Scheme.{u}} {M : X.Modules} {V : X.Opens} {d : ℕ} (f f' : Fin d → Γ(M, V))
    (a : Matrix (Fin d) (Fin d) Γ(X, V)) (h : ∀ j, f' j = ∑ i, a i j • f i) :
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower X d).obj M.val)).app (op V)
      (show ((Scheme.Modules.presheafExteriorPower X d).obj M.val).obj (op V) from exteriorPower.ιMulti Γ(X, V) d f') :
      Γ(Scheme.Modules.det d M, V)) =
    a.det • (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower X d).obj M.val)).app (op V)
      (show ((Scheme.Modules.presheafExteriorPower X d).obj M.val).obj (op V) from exteriorPower.ιMulti Γ(X, V) d f) :
      Γ(Scheme.Modules.det d M, V)) := by
  have key := Scheme.Modules.exteriorPower_map_app_unit_iotaMulti_eq_det_smul (𝟙 M) (U := V) f' f a
    (fun j => by rw [h j]; rfl)
  rw [CategoryTheory.Functor.map_id] at key
  exact key
