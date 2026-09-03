import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_isBoundedOnSiegelWindows_weightOneLift
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne

theorem LanglandsTunnell.isBoundedOnSiegelWindows_weightOneLift
    {n : ℕ} (f : ℍ → ℂ)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2)) :
    IsBoundedOnSiegelWindows ℚ (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_isBoundedOnSiegelWindows_weightOneLift.solution
