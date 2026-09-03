import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import P2M.Util
namespace P2MW.S_AutomorphicForm_ideleNorm_det_globalPoints

set_option autoImplicit false

open scoped NumberField

theorem solution
    {F : Type} [Field F] [NumberField F] (γ : Matrix.GeneralLinearGroup (Fin 2) F) :
    NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 F) F γ)) = 1 := by
  have hdet : Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 F) F γ)
      = Units.map (algebraMap F (NumberField.AdeleRing (𝓞 F) F)).toMonoidHom
          (Matrix.GeneralLinearGroup.det γ) := by
    refine Units.ext ?_
    rw [Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.val_det_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      RingHom.map_det]
    rfl
  letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  unfold NumberField.TateGlobal.ideleNorm
  rw [hdet, NumberField.AdeleRing.distribHaarChar_algebraMap F (Matrix.GeneralLinearGroup.det γ)]
  rfl
