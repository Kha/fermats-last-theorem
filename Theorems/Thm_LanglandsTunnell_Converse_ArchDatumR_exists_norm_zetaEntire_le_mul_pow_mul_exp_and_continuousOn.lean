import Definitions.Def_LanglandsTunnell_JLConverse
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumR_exists_norm_zetaEntire_le_mul_pow_mul_exp_and_continuousOn

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.ArchDatumR.exists_norm_zetaEntire_le_mul_pow_mul_exp_and_continuousOn
    {P : RealArchParam} (D : ArchDatumR P) (u : ℂ) (a : ZMod 2) :
    (∀ σ₁ σ₂ : ℝ, ∃ (C A : ℝ) (N : ℕ), ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
        ‖D.zetaEntire g u a s‖ ≤
          C * (1 + |g 0 0| + |g 0 1| + |g 1 0| + |g 1 1| + |g.det|⁻¹) ^ N * Real.exp (A * |s.im|)) ∧
    ∀ s : ℂ, ContinuousOn (fun M : Fin 2 → Fin 2 → ℝ => D.zetaEntire (Matrix.of M) u a s) ArchR.glSet := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_norm_zetaEntire_le_mul_pow_mul_exp_and_continuousOn.solution
