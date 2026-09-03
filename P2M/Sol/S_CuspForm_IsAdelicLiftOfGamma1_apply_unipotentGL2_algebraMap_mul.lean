import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicTraceProducer
import P2M.Util
namespace P2MW.S_CuspForm_IsAdelicLiftOfGamma1_apply_unipotentGL2_algebraMap_mul

set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicBox NumberField.StandardAddChar AutomorphicForm

theorem solution
    {M : ℕ} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = Φ g := by
  have key : unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) =
      AutomorphicForm.globalPoints (𝓞 ℚ) ℚ (unipotentGL2 β) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AutomorphicForm.globalPoints, unipotentGL2, Matrix.GeneralLinearGroup.map]
  rw [key]
  exact hΦ.left_inv _ _
