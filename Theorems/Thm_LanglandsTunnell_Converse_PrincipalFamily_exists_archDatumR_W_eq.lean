import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_PrincipalFamily_exists_archDatumR_W_eq
attribute [-simp] LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply

set_option autoImplicit false

open LanglandsTunnell.Converse LanglandsTunnell.Converse.PrincipalFamily

theorem LanglandsTunnell.Converse.PrincipalFamily.exists_archDatumR_W_eq (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    ∃ D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂), D.W = Wmem u₁ u₂ a₁ a₂ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_PrincipalFamily_exists_archDatumR_W_eq.solution
