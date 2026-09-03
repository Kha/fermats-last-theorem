import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
namespace P2MW.S_AutomorphicForm_CuspidalConstituent_eq_of_isCuspConstituent_of_exists_mem_ne_zero

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (h₁ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F pins ξ V₁)
    (h₂ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F pins ξ V₂)
    (h : ∃ φ ∈ V₁ ⊓ V₂, φ ≠ 0) : V₁ = V₂ := by
  obtain ⟨φ, hφ, hφ0⟩ := h
  have hsub : AutomorphicForm.CuspidalConstituent.IsCuspSubrep F pins ξ (V₁ ⊓ V₂) :=
    { le := inf_le_left.trans h₁.1.le
      rightTranslate_fin_mem := fun g hg ψ hψ =>
        ⟨h₁.1.rightTranslate_fin_mem g hg ψ hψ.1, h₂.1.rightTranslate_fin_mem g hg ψ hψ.2⟩
      rightTranslate_arch_mem := fun w k ψ hψ =>
        ⟨h₁.1.rightTranslate_arch_mem w k ψ hψ.1, h₂.1.rightTranslate_arch_mem w k ψ hψ.2⟩
      rightConv_mem := fun f tys hf hbi ψ hψ =>
        ⟨h₁.1.rightConv_mem f tys hf hbi ψ hψ.1, h₂.1.rightConv_mem f tys hf hbi ψ hψ.2⟩ }
  have hne : V₁ ⊓ V₂ ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.mem_bot] at hφ
    exact hφ0 hφ
  have e₁ : V₁ ⊓ V₂ = V₁ := (h₁.2.2 _ hsub inf_le_left).resolve_left hne
  have e₂ : V₁ ⊓ V₂ = V₂ := (h₂.2.2 _ hsub inf_le_right).resolve_left hne
  exact e₁.symm.trans e₂
