import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_modulus_complex_eq_nnnorm_sq

set_option autoImplicit false
open LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.modulus_complex_eq_nnnorm_sq :
    ∀ (z : ℂ), modulus z = ‖z‖₊ ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_modulus_complex_eq_nnnorm_sq.solution
