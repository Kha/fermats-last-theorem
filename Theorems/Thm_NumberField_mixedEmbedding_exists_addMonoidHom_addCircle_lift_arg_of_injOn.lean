import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_exists_addMonoidHom_addCircle_lift_arg_of_injOn

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical in

theorem NumberField.mixedEmbedding.exists_addMonoidHom_addCircle_lift_arg_of_injOn
    (K : Type) [Field K] [NumberField K] {c : ℕ}
    (arg : mixedSpace K → (Fin (nrComplexPlaces K) → ℝ))
    (harg : ∀ y y' : mixedSpace K, IsUnit y → IsUnit y' →
      ∃ k : Fin (nrComplexPlaces K) → ℤ, arg (y * y') = arg y + arg y' + fun j => (k j : ℝ))
    (F : Subgroup Kˣ)
    (L : Kˣ → (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin c → ℤ))
    (hL_mul : ∀ φ ∈ F, ∀ ψ ∈ F, L (φ * ψ) = L φ + L ψ)
    (hL_inj : ∀ φ ∈ F, L φ = 0 → φ = 1)
    (Λ : AddSubgroup ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin c → ℤ)))
    (hΛ : ∀ γ, γ ∈ Λ ↔ ∃ φ ∈ F, L φ = γ)
    (b : Fin c → ℝ) :
    ∃ (χ : Λ →+ (Fin (Fintype.card (InfinitePlace K) + c) → AddCircle (1 : ℝ)))
      (lift : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin c → ℤ) →
        (Fin (Fintype.card (InfinitePlace K) + c) → ℝ)),
      lift 0 = 0 ∧
      (∀ (γ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin c → ℤ)) (hγ : γ ∈ Λ)
          (j : Fin (Fintype.card (InfinitePlace K) + c)), ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j) ∧
      ∀ φ ∈ F,
        (∀ w : {w : InfinitePlace K // w.IsComplex},
          ((lift (L φ) (Fin.castAdd c (Fintype.equivFin (InfinitePlace K) w.1)) : ℝ) : AddCircle (1 : ℝ)) =
            ((arg (mixedEmbedding K (φ : K)) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} w) : ℝ) :
              AddCircle (1 : ℝ))) ∧
        (∀ j : Fin c,
          ((lift (L φ) (Fin.natAdd (Fintype.card (InfinitePlace K)) j) : ℝ) : AddCircle (1 : ℝ)) =
            ((b j * ((L φ).2 j : ℝ) : ℝ) : AddCircle (1 : ℝ))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_exists_addMonoidHom_addCircle_lift_arg_of_injOn.solution
