import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 K) K μ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) :
    ∃ t : ℕ, ∀ v : HeightOneSpectrum (𝓞 ℚ),
      ¬ IsBadPlace K μ v →
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1) →
      (∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1) →
      ∀ W : LocalGL3 v → ℂ,
      IsGL3PsiWhittakerFn (psiLoc ψ v) W ∧
      IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v W →
      ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1 →
        ‖W h‖ ≤ 1 / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar.solution
