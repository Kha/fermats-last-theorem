import Definitions.Def_LanglandsTunnell_QuatH
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_not_isGalois_fixFld_sylowH

set_option autoImplicit false

theorem LanglandsTunnell.not_isGalois_fixFld_sylowH {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ¬ IsGalois ℚ ↥(fixFld (sylowH e)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_not_isGalois_fixFld_sylowH.solution
