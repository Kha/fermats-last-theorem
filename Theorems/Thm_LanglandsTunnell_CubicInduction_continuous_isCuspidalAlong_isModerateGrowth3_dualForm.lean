import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_continuous_isCuspidalAlong_isModerateGrowth3_dualForm

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.continuous_isCuspidalAlong_isModerateGrowth3_dualForm
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hc : Continuous Φ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Φ g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      Φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * Φ g)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) Φ)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) Φ)
    (hmg : IsModerateGrowth3 ℚ Φ) :
    Continuous (dualForm Φ) ∧
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), dualForm Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = dualForm Φ g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        dualForm Φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ)⁻¹ * dualForm Φ g) ∧
      IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) (dualForm Φ) ∧
      IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) (dualForm Φ) ∧
      IsModerateGrowth3 ℚ (dualForm Φ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_continuous_isCuspidalAlong_isModerateGrowth3_dualForm.solution
