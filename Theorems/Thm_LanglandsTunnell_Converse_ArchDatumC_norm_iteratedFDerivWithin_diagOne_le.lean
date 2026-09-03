import Definitions.Def_LanglandsTunnell_JLConverse
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumC_norm_iteratedFDerivWithin_diagOne_le

set_option autoImplicit false
open LanglandsTunnell LanglandsTunnell.Converse in

theorem LanglandsTunnell.Converse.ArchDatumC.norm_iteratedFDerivWithin_diagOne_le
    (P : ComplexArchParam) (d : ArchDatumC P) (c₀ : ℝ)
    (hc₀ : ∀ k : ℤ, ∀ ν ∈ (P.twist 0 k).gammaC, -ν.re < c₀)
    (M : ℕ) :
    ∃ C : ℝ, ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), ArchC.IsK k → z ≠ 0 → ‖z‖ ≤ 1 →
      ‖iteratedFDerivWithin ℝ M (ArchC.asPi d.W) ArchC.glSet (ArchC.diagOneMulCoords z k)‖
        ≤ C * ‖z‖ ^ (2 * (1 - c₀) - (M : ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumC_norm_iteratedFDerivWithin_diagOne_le.solution
