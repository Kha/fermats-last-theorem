import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_continuous_and_isGaugeMajorised3_of_eq_mul_prod

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.continuous_and_isGaugeMajorised3_of_eq_mul_prod
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hfac : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W g = Warch (archComponent3 (𝓞 ℚ) ℚ g) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v g))
    (hinv : ∀ v, v ∉ S → IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (Wloc v))
    (hsph : ∃ t : ℕ, ∀ v, v ∉ S → ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1) → Wloc v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1 →
        ‖Wloc v h‖ ≤ 1 / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (hS : ∀ v ∈ S,
      (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, Wloc v (g * k) = Wloc v g) ∧
      ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
          (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → Wloc v h = 0) ∧
          (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
            ‖Wloc v h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (harch : Continuous Warch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) :
    Continuous W ∧ IsGaugeMajorised3 ℚ W := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_continuous_and_isGaugeMajorised3_of_eq_mul_prod.solution
