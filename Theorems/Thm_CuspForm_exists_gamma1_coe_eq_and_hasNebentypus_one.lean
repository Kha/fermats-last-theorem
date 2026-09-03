import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_CuspForm_exists_gamma1_coe_eq_and_hasNebentypus_one

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

theorem CuspForm.exists_gamma1_coe_eq_and_hasNebentypus_one
    {M : ℕ} (k : ℤ) (g : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    ∃ g₁ : CuspForm (CongruenceSubgroup.Gamma1 M) k,
      (⇑g₁ : UpperHalfPlane → ℂ) = ⇑g ∧ CuspForm.HasNebentypus (1 : DirichletCharacter ℂ M) g₁ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_gamma1_coe_eq_and_hasNebentypus_one.solution
