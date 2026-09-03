import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsBadPlace K μ v)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1) :
    ∃ W : LocalGL3 v → ℂ,
      IsGL3PsiWhittakerFn (psiLoc ψ v) W ∧
      IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v W := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace.solution
