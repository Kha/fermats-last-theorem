import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_span_eq_top_forall_exists_algebraMap_comp_eq_comp_of_bijective_tensorProduct

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem Algebra.exists_span_eq_top_forall_exists_algebraMap_comp_eq_comp_of_bijective_tensorProduct
    (𝒪 : Type u) [CommRing 𝒪] (𝒪' : Type u) [CommRing 𝒪'] [Algebra 𝒪 𝒪']
    (G : Type) [Group G] [Finite G] (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪'))
    (hgal : Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
      Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
        (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪') ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x))
    (S : Type u) [CommRing S] (s₁ s₂ : 𝒪' →+* S)
    (hs : s₁.comp (algebraMap 𝒪 𝒪') = s₂.comp (algebraMap 𝒪 𝒪')) :
    ∃ (k : ℕ) (r : Fin k → S), Ideal.span (Set.range r) = ⊤ ∧ ∀ i : Fin k, ∃ σ : G,
      (algebraMap S (Localization.Away (r i))).comp s₂ =
        (algebraMap S (Localization.Away (r i))).comp (s₁.comp ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_span_eq_top_forall_exists_algebraMap_comp_eq_comp_of_bijective_tensorProduct.solution
