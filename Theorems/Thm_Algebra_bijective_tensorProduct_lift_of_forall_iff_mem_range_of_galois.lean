import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_bijective_tensorProduct_lift_of_forall_iff_mem_range_of_galois

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u v

theorem Algebra.bijective_tensorProduct_lift_of_forall_iff_mem_range_of_galois
    (𝒪 : Type u) [CommRing 𝒪] (𝒪' : Type u) [CommRing 𝒪'] [Algebra 𝒪 𝒪'] [Module.Flat 𝒪 𝒪']
    (G : Type v) [Group G] [Finite G] (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪'))
    (hgal : Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
      Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
        (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪') ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x))
    (A : Type u) [CommRing A] [Algebra 𝒪' A] [Algebra 𝒪 A] [IsScalarTower 𝒪 𝒪' A]
    (θ : G → (A ≃+* A)) (hθ1 : θ 1 = RingEquiv.refl A) (hθmul : ∀ σ σ' : G, θ (σ * σ') = (θ σ').trans (θ σ))
    (hθτ : ∀ (σ : G) (l : 𝒪') (a : A), θ σ (algebraMap 𝒪' A l * a) = algebraMap 𝒪' A (τ σ l) * θ σ a)
    (C : Type u) [CommRing C] [Algebra 𝒪 C] (ι : C →ₐ[𝒪] A) (hι : Function.Injective ι)
    (hιG : ∀ a : A, (∀ σ : G, θ σ a = a) ↔ a ∈ Set.range ι) :
    Function.Bijective (Algebra.TensorProduct.lift (ι : C →ₐ[𝒪] A) (IsScalarTower.toAlgHom 𝒪 𝒪' A)
      (fun c l => Commute.all _ _) : C ⊗[𝒪] 𝒪' →ₐ[𝒪] A) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_bijective_tensorProduct_lift_of_forall_iff_mem_range_of_galois.solution
