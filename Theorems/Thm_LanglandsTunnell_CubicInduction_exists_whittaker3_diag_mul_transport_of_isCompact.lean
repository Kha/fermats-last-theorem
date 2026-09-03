import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_whittaker3_diag_mul_transport_of_isCompact
attribute [-instance] WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing
attribute [-simp] LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.exists_whittaker3_diag_mul_transport_of_isCompact
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : Continuous u)
    (h2 : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g)
    (h3 : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hK : IsCompact K) :
    ∃ (lam₀ nB Ω : ℝ) (K₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)), 0 < lam₀ ∧ lam₀ ≤ 1 ∧ 0 ≤ nB ∧ 0 ≤ Ω ∧ IsCompact K₀ ∧
      (∀ k' ∈ K₀, archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3) ∧
      ∀ g ∈ K, ∃ (lam τ n₁ n₂ : ℝ) (κ₁ : ℂ) (k' : AdelicGL 3 (𝓞 ℚ) ℚ), k' ∈ K₀ ∧
        lam₀ ≤ lam ∧ lam ≤ lam₀⁻¹ ∧ lam₀ ≤ τ ∧ τ ≤ lam₀⁻¹ ∧ |n₁| ≤ nB ∧ |n₂| ≤ nB ∧ ‖κ₁‖ ≤ Ω ∧
        ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * g) =
            κ₁ * Complex.exp (2 * Real.pi * Complex.I * ((y₁ * n₁ + y₂ * n₂ : ℝ) : ℂ)) *
              whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                NumberField.StandardAddChar.psiQ u
                (WhittakerBlock.archRealLift3
                    (fun i j => if i = j then ![lam * y₁ * (τ * y₂), τ * y₂, 1] i else 0) * k') := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker3_diag_mul_transport_of_isCompact.solution
