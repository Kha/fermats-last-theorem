import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_cyclotomic_galois_cover_of_isUnit

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem Algebra.exists_cyclotomic_galois_cover_of_isUnit
    (𝒪 : Type) [CommRing 𝒪] (m : ℕ) (hm : 0 < m) (hmu : IsUnit ((m : ℕ) : 𝒪)) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : Algebra 𝒪 𝒪'),
      Module.Finite 𝒪 𝒪' ∧ Module.Free 𝒪 𝒪' ∧ Module.FaithfullyFlat 𝒪 𝒪' ∧
      (∃ ζ : 𝒪', ζ ^ m = 1 ∧ ∀ j : ℕ, 0 < j → j < m → IsUnit (1 - ζ ^ j)) ∧
      (∀ (S : Type) [CommRing S] [Algebra 𝒪 S], Module.FaithfullyFlat S (S ⊗[𝒪] 𝒪') ∧ Algebra.Etale S (S ⊗[𝒪] 𝒪')) ∧
      ∃ (G : Type) (_ : Group G) (_ : Finite G) (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪')),
        (Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
          Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
            (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪') ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x)) ∧
        (∀ (S : Type) [CommRing S] (s₁ s₂ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪')),
          s₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) = s₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) →
          ∃ (k : ℕ) (r : Fin k → S), Ideal.span (Set.range r) = ⊤ ∧ ∀ i : Fin k, ∃ σ : G,
            Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ s₂ =
              Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ s₁ ≫
                Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪'))) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_cyclotomic_galois_cover_of_isUnit.solution
