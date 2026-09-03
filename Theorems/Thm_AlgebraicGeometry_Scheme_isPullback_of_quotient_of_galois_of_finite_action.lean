import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_isPullback_of_quotient_of_galois_of_finite_action

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u v

theorem AlgebraicGeometry.Scheme.isPullback_of_quotient_of_galois_of_finite_action
    (𝒪 : Type) [CommRing 𝒪] (𝒪' : Type) [CommRing 𝒪'] [Algebra 𝒪 𝒪'] [Module.Finite 𝒪 𝒪'] [Module.Free 𝒪 𝒪']
    [Module.FaithfullyFlat 𝒪 𝒪']
    (G : Type) [Group G] [Finite G] (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪'))
    (hgal : Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
      Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
        (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪') ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x))
    (M' : Scheme.{0}) (πM' : M' ⟶ Spec (CommRingCat.of 𝒪'))
    (ρ : G → (M' ≅ M')) (hρ1 : (ρ 1).hom = 𝟙 M') (hρmul : ∀ σ σ' : G, (ρ (σ * σ')).hom = (ρ σ).hom ≫ (ρ σ').hom)
    (hρπ : ∀ σ : G, (ρ σ).hom ≫ πM' = πM' ≫ Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (q : M' ⟶ M)
    (hq : ∀ σ : G, (ρ σ).hom ≫ q = q)
    (hqπ : q ≫ πM = πM' ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')))
    (haff : IsAffineHom q)
    (hinj : ∀ V : M.Opens, Function.Injective (q.app V))
    (hrange : ∀ V : M.Opens, Set.range (q.app V) =
      {t | ∀ σ : G, (ρ σ).hom.appLE (q ⁻¹ᵁ V) (q ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, hq σ]) t = t}) :
    CategoryTheory.IsPullback q πM' πM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪'))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_isPullback_of_quotient_of_galois_of_finite_action.solution
