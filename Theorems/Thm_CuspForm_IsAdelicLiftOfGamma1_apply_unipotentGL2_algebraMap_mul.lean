import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicTraceProducer
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOfGamma1_apply_unipotentGL2_algebraMap_mul

set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicBox NumberField.StandardAddChar AutomorphicForm

theorem CuspForm.IsAdelicLiftOfGamma1.apply_unipotentGL2_algebraMap_mul
    {M : ℕ} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = Φ g := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOfGamma1_apply_unipotentGL2_algebraMap_mul.solution
