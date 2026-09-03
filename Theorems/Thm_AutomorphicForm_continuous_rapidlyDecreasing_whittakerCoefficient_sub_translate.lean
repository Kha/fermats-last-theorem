import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import P2M.Util
import P2M.Sol.S_AutomorphicForm_continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm LanglandsTunnell.RankinSelberg

theorem AutomorphicForm.continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate
    (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (h : AdelicGL2 (𝓞 F) F) :
    ((Continuous φ → Continuous fun g => φ (g * h) - φ g) ∧
    (IsRapidlyDecreasingOnSiegelSets F φ → IsRapidlyDecreasingOnSiegelSets F fun g => φ (g * h) - φ g) ∧
    ((∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g) →
      ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        (fun g => φ (g * h) - φ g) (globalPoints (𝓞 F) F γ * g) = (fun g => φ (g * h) - φ g) g) ∧
    (∀ ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ,
      (∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F), φ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ g) →
      ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
        (fun g => φ (g * h) - φ g) (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * (fun g => φ (g * h) - φ g) g) ∧
    (∀ (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F),
      WhittakerCoefficientIntegrable F pins ψ φ α (g * h) → WhittakerCoefficientIntegrable F pins ψ φ α g →
        WhittakerCoefficientIntegrable F pins ψ (fun g => φ (g * h) - φ g) α g ∧
        whittakerCoefficient F pins ψ (fun g => φ (g * h) - φ g) α g =
          whittakerCoefficient F pins ψ φ α (g * h) - whittakerCoefficient F pins ψ φ α g) ∧
    (∀ (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (g : AdelicGL2 (𝓞 F) F),
      (∀ α : F, WhittakerCoefficientIntegrable F pins ψ φ α (g * h)) →
      (∀ α : F, WhittakerCoefficientIntegrable F pins ψ φ α g) →
      (Summable fun α : F => ‖whittakerCoefficient F pins ψ φ α (g * h)‖) →
      (Summable fun α : F => ‖whittakerCoefficient F pins ψ φ α g‖) →
        Summable fun α : F => ‖whittakerCoefficient F pins ψ (fun g => φ (g * h) - φ g) α g‖) ∧
    (∀ (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F)
      {β γ : Type} [Mul γ] (r : AdelicGL2 (𝓞 F) F → β) (f : AdelicGL2 (𝓞 F) F → γ) (h' : γ)
      (WA : β → ℂ) (Wf : γ → ℂ),
      (∀ g : AdelicGL2 (𝓞 F) F, r (g * h) = r g) → (∀ g : AdelicGL2 (𝓞 F) F, f (g * h) = f g * h') →
      (∀ g : AdelicGL2 (𝓞 F) F, WhittakerCoefficientIntegrable F pins ψ φ α g) →
      (∀ g : AdelicGL2 (𝓞 F) F, whittakerCoefficient F pins ψ φ α g = WA (r g) * Wf (f g)) →
        ∀ g : AdelicGL2 (𝓞 F) F,
          whittakerCoefficient F pins ψ (fun g => φ (g * h) - φ g) α g = WA (r g) * (Wf (f g * h') - Wf (f g)))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate.solution
