import Mathlib
import P2M.Util
import P2M.Sol.S_HomogeneousIdeal_irrelevant_le_map_of_forall_le_span_image

set_option autoImplicit false

universe u

theorem HomogeneousIdeal.irrelevant_le_map_of_forall_le_span_image
    {S : Type u} [CommRing S] {S' : Type u} [CommRing S']
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (R' : Type u) [CommRing R'] [Algebra S' R'] (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ϑ : R →+* R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hspan : ∀ n, 0 < n → 𝓡' n ≤ Submodule.span S' (ϑ '' (𝓡 n : Set R))) :
    HomogeneousIdeal.irrelevant 𝓡' ≤
      (HomogeneousIdeal.irrelevant 𝓡).map ({ ϑ with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') := by p2m_exact_reverting @_root_.P2MW.S_HomogeneousIdeal_irrelevant_le_map_of_forall_le_span_image.solution
