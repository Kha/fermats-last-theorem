import Definitions.Def_LanglandsTunnell_JLConverse
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumR_norm_iteratedFDerivWithin_diagOne_le

set_option autoImplicit false
open LanglandsTunnell LanglandsTunnell.Converse in

theorem LanglandsTunnell.Converse.ArchDatumR.norm_iteratedFDerivWithin_diagOne_le
    (P : RealArchParam) (d : ArchDatumR P) (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (M : ℕ) :
    ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 → |y| ≤ 1 →
      ‖iteratedFDerivWithin ℝ M (ArchR.asPi d.W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖
        ≤ C * |y| ^ (1 - c₀ - (M : ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumR_norm_iteratedFDerivWithin_diagOne_le.solution
