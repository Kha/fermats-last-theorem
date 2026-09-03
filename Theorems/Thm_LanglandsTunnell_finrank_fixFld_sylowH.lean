import Definitions.Def_LanglandsTunnell_C8Tower
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_finrank_fixFld_sylowH

set_option autoImplicit false

open NumberField LanglandsTunnell

theorem LanglandsTunnell.finrank_fixFld_sylowH {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ℚ ↥(fixFld (sylowH e)) = 3 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_finrank_fixFld_sylowH.solution
