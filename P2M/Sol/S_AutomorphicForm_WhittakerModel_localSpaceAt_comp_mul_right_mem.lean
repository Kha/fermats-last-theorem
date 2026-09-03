import Mathlib
import Definitions.Def_AutomorphicForm_WhittakerModelMultiplicityOne
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
namespace P2MW.S_AutomorphicForm_WhittakerModel_localSpaceAt_comp_mul_right_mem

set_option autoImplicit false

noncomputable section

namespace WfOneP2

theorem localFnAt_mul_right
    (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ)
    (g k : GL (Fin 2) (v.adicCompletion ℚ)) :
    AutomorphicForm.WhittakerModel.localFnAt ℚ pins ψ v (fun y => φ (y * h)) (g * k) =
      AutomorphicForm.WhittakerModel.localFnAt ℚ pins ψ v
        (fun y => φ (y * (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
          (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v k) * h))) g := by
  simp only [AutomorphicForm.WhittakerModel.localFnAt, AutomorphicForm.whittakerCoefficient, map_mul,
    mul_assoc]

theorem mul_right_mem_localSpaceAt
    (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (W : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW : W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ v φ)
    (k : GL (Fin 2) (v.adicCompletion ℚ)) :
    (fun g => W (g * k)) ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ v φ := by
  induction hW using Submodule.span_induction with
  | mem W hWmem =>
    obtain ⟨h, rfl⟩ := hWmem
    refine Submodule.subset_span ⟨AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
      (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v k) * h, ?_⟩
    funext g
    exact localFnAt_mul_right pins ψ v φ h g k
  | zero =>
    exact (AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ v φ).zero_mem
  | add W₁ W₂ _ _ h₁ h₂ =>
    exact (AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ v φ).add_mem h₁ h₂
  | smul c W _ h₁ =>
    exact (AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ v φ).smul_mem c h₁

end WfOneP2

end

open IsDedekindDomain NumberField AutomorphicForm in
theorem solution
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ p φ,
      ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ p φ :=
  fun W hW h => WfOneP2.mul_right_mem_localSpaceAt pins ψ p φ W hW h
