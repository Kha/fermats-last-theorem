import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_PrincipalFamily_isCasimirEigen_of_W_eq_comb
attribute [-simp] LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchCasimir

theorem LanglandsTunnell.Converse.PrincipalFamily.isCasimirEigen_of_W_eq_comb {u₁ u₂ : ℂ} {a₁ a₂ : ZMod 2}
    (D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂)) (c₁ c₂ : ℂ) (e₁ e₂ : ℕ) (p₁ p₂ q₁ q₂ : ZMod 2)
    (hW : D.W = fun g => c₁ * ((SignType.sign g.det : ℝ) : ℂ) ^ e₁ * PrincipalFamily.Wmem u₁ u₂ p₁ p₂ g +
      c₂ * ((SignType.sign g.det : ℝ) : ℂ) ^ e₂ * PrincipalFamily.Wmem u₁ u₂ q₁ q₂ g) :
    IsCasimirEigen D := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_PrincipalFamily_isCasimirEigen_of_W_eq_comb.solution
