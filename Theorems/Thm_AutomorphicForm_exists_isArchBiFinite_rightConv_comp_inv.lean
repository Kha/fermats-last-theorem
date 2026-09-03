import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isArchBiFinite_rightConv_comp_inv

set_option autoImplicit false

open NumberField MeasureTheory AutomorphicForm

theorem AutomorphicForm.exists_isArchBiFinite_rightConv_comp_inv
    (F : Type) [Field F] [NumberField F]
    (f f' : AdelicGL2 (𝓞 F) F → ℂ) (tys tys' : ArchTypeFamily F)
    (hfc : Continuous f) (hfs : HasCompactSupport f) (hbf : IsArchBiFinite F tys f)
    (hfc' : Continuous f') (hfs' : HasCompactSupport f') (hbf' : IsArchBiFinite F tys' f') :
    ∃ tys'' : ArchTypeFamily F, IsArchBiFinite F tys'' (rightConv F f' (fun x => f x⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isArchBiFinite_rightConv_comp_inv.solution
