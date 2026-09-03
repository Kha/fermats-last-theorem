import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsPrincipalInvariantAddChar ℚ ψ)
    (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hΦ : ∀ (x y z : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) x) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) y)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) z) * g) = Φ g) :
    IsGL3PsiWhittakerFn ψ (whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq.solution
