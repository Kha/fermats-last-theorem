import Mathlib
import Definitions.Def_NumberField_CompletedRayL
import P2M.Util
import P2M.Sol.S_NumberField_exists_completedRayL_functionalEquation_of_primitive

set_option autoImplicit false

open NumberField NumberField.InfinitePlace Deep.NTSupply

universe u

open scoped Classical in

theorem NumberField.exists_completedRayL_functionalEquation_of_primitive
    (K : Type u) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (S : Finset {w : InfinitePlace K // w.IsReal})
    (hpar : ∀ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
      α - 1 ∈ 𝔣 →
        χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) =
          ∏ w ∈ S, ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ))
    (hprim : ∀ 𝔣' : Ideal (𝓞 K), 𝔣 ≤ 𝔣' → 𝔣' ≠ 𝔣 →
      ∃ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
        α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
          χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) ≠ 1) :
    ∃ (W : ℂ) (Λ Λ' : ℂ → ℂ), W ≠ 0 ∧ Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (∀ s : ℂ, 1 < s.re →
        Λ s = (if χ = 1 then s * (s - 1) else 1) * M4aTorus.completedRayL K 𝔣 χ S s ∧
        Λ' s = (if χ = 1 then s * (s - 1) else 1) *
          M4aTorus.completedRayL K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S s) ∧
      (∀ s : ℂ, Λ (1 - s) = W * Λ' s) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_completedRayL_functionalEquation_of_primitive.solution
