import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped ENNReal

theorem AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (g : AdelicGL2 (𝓞 F) F → ℂ) (hg : Continuous g)
    (α : AdelicGL2 (𝓞 F) F → ℂ) (hα : IsFactorizableTestFn F α) (hαt : IsArchBiFinite F tys α) :
    rightConv F g α ∈ archCutSubmodule F tys := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite.solution
