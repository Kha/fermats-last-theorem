import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
p2m_open "NumberField.AdelicHaar~isMulRightInvariant_adelicGLHaar NumberField.AdelicLevel NumberField.AdelicBox"
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj
    (F : Type) [Field F] [NumberField F]
    (h : AdelicGL2 (𝓞 F) F) (φ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F (rightTranslate F h φ) f = rightTranslate F h (rightConv F φ (fun y => f (h * y * h⁻¹))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj.solution
