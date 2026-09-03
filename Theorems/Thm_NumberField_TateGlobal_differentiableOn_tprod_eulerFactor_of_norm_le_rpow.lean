import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_differentiableOn_tprod_eulerFactor_of_norm_le_rpow

set_option autoImplicit false

open NumberField NumberField.TateGlobal IsDedekindDomain AutomorphicForm Polynomial

open scoped Classical in

theorem NumberField.TateGlobal.differentiableOn_tprod_eulerFactor_of_norm_le_rpow
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (a b : HeightOneSpectrum (𝓞 F) → ℂ)
    (τ : ℝ)
    (hτ : ∀ v ∉ S, ‖((χ (uniformizerIdele F v) : ℂˣ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ τ)
    (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ‖a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖b v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (σ₀ : ℝ) (hσ₀ : κ + τ + 4 ≤ σ₀) :
    (∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
        ((if IsUnramifiedCharAt χ v.1
          then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * a v.1) * X
            + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * b v.1) * X ^ 2
          else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
        (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          ((if IsUnramifiedCharAt χ v.1
            then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * a v.1) * X
              + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * b v.1) * X ^ 2
            else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)) ∧
    DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        ((if IsUnramifiedCharAt χ v.1
          then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * a v.1) * X
            + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * b v.1) * X ^ 2
          else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
      {s : ℂ | σ₀ < s.re} := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_differentiableOn_tprod_eulerFactor_of_norm_le_rpow.solution
