import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_FnTwist3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.Converse

theorem LanglandsTunnell.CubicInduction.continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : Continuous form)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = form g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * form g)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) form)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) form)
    (hmg : IsModerateGrowth3 ℚ form)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ) :
    Continuous (fnTwist3 (𝓞 ℚ) ℚ χ form) ∧
    (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      fnTwist3 (𝓞 ℚ) ℚ χ form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) =
        fnTwist3 (𝓞 ℚ) ℚ χ form g) ∧
    (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      fnTwist3 (𝓞 ℚ) ℚ χ form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) =
        (twistedCentralChar3 (𝓞 ℚ) ℚ ω χ z : ℂ) * fnTwist3 (𝓞 ℚ) ℚ χ form g) ∧
    IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) (fnTwist3 (𝓞 ℚ) ℚ χ form) ∧
    IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) (fnTwist3 (𝓞 ℚ) ℚ χ form) ∧
    IsModerateGrowth3 ℚ (fnTwist3 (𝓞 ℚ) ℚ χ form) ∧
    ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ (fnTwist3 (𝓞 ℚ) ℚ χ form) g =
        chiDetGL 3 (𝓞 ℚ) ℚ χ g * whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ form g := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul.solution
