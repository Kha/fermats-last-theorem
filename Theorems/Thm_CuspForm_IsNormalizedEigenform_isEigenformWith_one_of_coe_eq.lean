import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_isEigenformWith_one_of_coe_eq

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

theorem CuspForm.IsNormalizedEigenform.isEigenformWith_one_of_coe_eq
    {N : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g.IsNormalizedEigenform)
    (g₁ : CuspForm (CongruenceSubgroup.Gamma1 N) 2) (hg₁ : (⇑g₁ : UpperHalfPlane → ℂ) = ⇑g) :
    CuspForm.IsEigenformWith (1 : DirichletCharacter ℂ N) g₁ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_isEigenformWith_one_of_coe_eq.solution
