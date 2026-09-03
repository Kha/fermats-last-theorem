import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_separabilityElement_residueField_tensor_of_separabilityElement

set_option autoImplicit false

open scoped TensorProduct

theorem IsLocalRing.exists_separabilityElement_residueField_tensor_of_separabilityElement
    (S : Type) [CommRing S] [IsLocalRing S] {Λ : Type} [Ring Λ]
    (e : (S ⊗[ℤ] Λ) ⊗[S] (S ⊗[ℤ] Λ)) (he₁ : LinearMap.mul' S (S ⊗[ℤ] Λ) e = 1)
    (he₂ : ∀ x : S ⊗[ℤ] Λ, TensorProduct.map (LinearMap.mulLeft S x) LinearMap.id e =
      TensorProduct.map LinearMap.id (LinearMap.mulRight S x) e) :
    ∃ eΛ : ((IsLocalRing.ResidueField S) ⊗[ℤ] Λ) ⊗[(IsLocalRing.ResidueField S)] ((IsLocalRing.ResidueField S) ⊗[ℤ] Λ),
      LinearMap.mul' (IsLocalRing.ResidueField S) ((IsLocalRing.ResidueField S) ⊗[ℤ] Λ) eΛ = 1 ∧
      ∀ x : (IsLocalRing.ResidueField S) ⊗[ℤ] Λ,
        TensorProduct.map (LinearMap.mulLeft (IsLocalRing.ResidueField S) x) LinearMap.id eΛ =
          TensorProduct.map LinearMap.id (LinearMap.mulRight (IsLocalRing.ResidueField S) x) eΛ := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_separabilityElement_residueField_tensor_of_separabilityElement.solution
