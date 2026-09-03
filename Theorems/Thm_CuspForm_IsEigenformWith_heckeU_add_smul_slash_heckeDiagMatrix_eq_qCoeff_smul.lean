import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_eq_qCoeff_smul

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

theorem CuspForm.IsEigenformWith.heckeU_add_smul_slash_heckeDiagMatrix_eq_qCoeff_smul
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    ModularForm.heckeU 2 p ⇑h + ε (p : ZMod M) • ((⇑h) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p)
      = ModularFormClass.qCoeff h p • ⇑h := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_eq_qCoeff_smul.solution
