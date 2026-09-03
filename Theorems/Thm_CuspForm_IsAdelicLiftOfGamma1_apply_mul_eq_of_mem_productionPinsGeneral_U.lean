import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOfGamma1_apply_mul_eq_of_mem_productionPinsGeneral_U

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

theorem CuspForm.IsAdelicLiftOfGamma1.apply_mul_eq_of_mem_productionPinsGeneral_U
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (g u : AdelicGL2 (𝓞 ℚ) ℚ) (hu : u ∈ (productionPinsGeneral ℚ).U (AdelicDock.ratLevel M)) :
    Φ (g * u) = Φ g := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOfGamma1_apply_mul_eq_of_mem_productionPinsGeneral_U.solution
