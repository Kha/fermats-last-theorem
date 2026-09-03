import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integrable_and_integral_mellin_mul_apply_borel_mul_eq_of_isInducedSection_of_flat

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm
open IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.integrable_and_integral_mellin_mul_apply_borel_mul_eq_of_isInducedSection_of_flat
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ s))
      (_hφflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        φ s (k : AdelicGL2 (𝓞 K) K) = φ 0 (k : AdelicGL2 (𝓞 K) K))
      (h : ℝ → ℂ) (_hh : ContDiff ℝ (⊤ : ℕ∞) h) (_hhc : HasCompactSupport h)
      (σ' : ℝ) (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K)
      (k : AdelicGL2 (𝓞 K) K) (_hk : k ∈ adelicMaximalCompact K),
    let c : ℂ → ℂ := fun s => ∫ u : ℝ, h u * Complex.exp (s * (u : ℂ))
    let r : ℝ := ((αm (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℝˣ) : ℝ) /
      ((αm (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℝˣ) : ℝ)
    Integrable (fun t : ℝ =>
      c ((σ' : ℂ) + (t : ℂ) * Complex.I) * φ ((σ' : ℂ) + (t : ℂ) * Complex.I) (b * k)) ∧
    ∫ t : ℝ, c ((σ' : ℂ) + (t : ℂ) * Complex.I) * φ ((σ' : ℂ) + (t : ℂ) * Complex.I) (b * k) =
      (((2 * Real.pi) : ℝ) : ℂ) *
        (((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
          ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
          ((Real.sqrt r : ℝ) : ℂ) * h (-Real.log r) * φ 0 k) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integrable_and_integral_mellin_mul_apply_borel_mul_eq_of_isInducedSection_of_flat.solution
