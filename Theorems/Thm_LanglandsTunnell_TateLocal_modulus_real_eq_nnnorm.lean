import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_modulus_real_eq_nnnorm

set_option autoImplicit false
open LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.modulus_real_eq_nnnorm :
    ∀ (x : ℝ), modulus x = ‖x‖₊ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_modulus_real_eq_nnnorm.solution
