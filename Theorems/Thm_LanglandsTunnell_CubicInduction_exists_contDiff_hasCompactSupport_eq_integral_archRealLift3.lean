import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_contDiff_hasCompactSupport_eq_integral_archRealLift3
attribute [-instance] WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing
attribute [-simp] LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

theorem
LanglandsTunnell.CubicInduction.exists_contDiff_hasCompactSupport_eq_integral_archRealLift3
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => φ (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (hz : IsCentreFinite φ) :
    ∃ α : (Fin 3 → Fin 3 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) α ∧ HasCompactSupport α ∧
      tsupport α ⊆ {e | (Matrix.of e).det ≠ 0} ∧
      ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g = ∫ h : Fin 3 → Fin 3 → ℝ, φ (g * WhittakerBlock.archRealLift3 h) * α h := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_contDiff_hasCompactSupport_eq_integral_archRealLift3.solution
