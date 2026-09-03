import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_whittaker3_eq_whittaker3_globalPointsGL_mul_of_forall_apply_eq_apply_mul

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.whittaker3_eq_whittaker3_globalPointsGL_mul_of_forall_apply_eq_apply_mul
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ ψ' : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsPrincipalInvariantAddChar ℚ ψ)
    (a : ℚ) (hψ' : ∀ x : AdeleRing (𝓞 ℚ) ℚ, ψ' x = ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * x))
    (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Φ g)
    (t : GL (Fin 3) ℚ) (ht : (t : Matrix (Fin 3) (Fin 3) ℚ) = Matrix.diagonal ![a ^ 2, a, 1])
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ' Φ g =
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ (globalPointsGL 3 (𝓞 ℚ) ℚ t * g) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_whittaker3_eq_whittaker3_globalPointsGL_mul_of_forall_apply_eq_apply_mul.solution
