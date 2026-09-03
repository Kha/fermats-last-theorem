import Mathlib
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_Algebra_PointDerivations_exists_reader_tensor_linearMap_dual_of_linearEquiv_tensor

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.PointDerivations.exists_reader_tensor_linearMap_dual_of_linearEquiv_tensor
    (κ : Type) [Field κ] (R : Type) [CommRing R] [Algebra κ R] (ev : R →+* κ)
    (W : Type) [AddCommGroup W] [Module κ W]
    (Φ : ∀ (M : Type) [AddCommGroup M] [Module κ M], ↥(Algebra.PointDerivations κ R ev M) ≃ₗ[κ] (W ⊗[κ] M))
    (hΦnat : ∀ (M M' : Type) [AddCommGroup M] [Module κ M] [AddCommGroup M'] [Module κ M'] (g : M →ₗ[κ] M')
        (δ : ↥(Algebra.PointDerivations κ R ev M)),
      Φ M' (Algebra.PointDerivations.map ev g δ) = _root_.TensorProduct.map (LinearMap.id : W →ₗ[κ] W) g (Φ M δ))
    {C₀ C₁ C₂ : Type} [AddCommGroup C₀] [Module κ C₀] [AddCommGroup C₁] [Module κ C₁] [AddCommGroup C₂] [Module κ C₂]
    (d₀ : C₀ →ₗ[κ] C₁) (d₁ : C₁ →ₗ[κ] C₂)
    (H₁ : Type) [AddCommGroup H₁] [Module κ H₁]
    (cls₁ : ↥(LinearMap.ker d₁) →ₗ[κ] H₁) (hcls₁ : Function.Surjective cls₁)
    (hcls₁0 : ∀ z : ↥(LinearMap.ker d₁), cls₁ z = 0 ↔ (z : C₁) ∈ LinearMap.range d₀)
    (V : Type) [AddCommGroup V] [Module κ V] [Module.Finite κ V] :
    ∃ Ψ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)) → W ⊗[κ] (Module.Dual κ V →ₗ[κ] H₁),

      (∀ c : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)),
        (∀ (a : R) (ξ : Module.Dual κ V), (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) →
        ∃ ĉ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))),
          ∀ (a : R) (ξ : Module.Dual κ V),
            (((ĉ : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))) a ξ : ↥(LinearMap.ker d₁)) : C₁) =
              (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ) ∧

      (∀ (c : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)))
          (ĉ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))),
        (∀ (a : R) (ξ : Module.Dual κ V),
            (((ĉ : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))) a ξ : ↥(LinearMap.ker d₁)) : C₁) =
              (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ) →
        Ψ c = Φ (Module.Dual κ V →ₗ[κ] H₁)
          (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))
            (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev (LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker d₁) H₁ cls₁) ĉ)) ∧

      (∀ c c' : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)),
        (∀ (a : R) (ξ : Module.Dual κ V), (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) →
        (∀ (a : R) (ξ : Module.Dual κ V), (c' : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) →
        (Ψ c = Ψ c' ↔
          ∀ (a : R) (ξ : Module.Dual κ V), ∃ b : C₀,
            d₀ b = (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ - (c' : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ)) ∧

      (∀ w : W ⊗[κ] (Module.Dual κ V →ₗ[κ] H₁),
        ∃ c : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)),
          (∀ (a : R) (ξ : Module.Dual κ V), (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) ∧ Ψ c = w) ∧

      (∀ (c c' : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁))) (φ : V →ₗ[κ] V)
          (T : (Module.Dual κ V →ₗ[κ] H₁) →ₗ[κ] (Module.Dual κ V →ₗ[κ] H₁)),
        (∀ (F : Module.Dual κ V →ₗ[κ] H₁) (ξ : Module.Dual κ V), T F ξ = F (ξ ∘ₗ φ)) →
        (∀ (a : R) (ξ : Module.Dual κ V), (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) →
        (∀ (a : R) (ξ : Module.Dual κ V),
            (c' : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ = (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a (ξ ∘ₗ φ)) →
        Ψ c' = _root_.TensorProduct.map (LinearMap.id : W →ₗ[κ] W) T (Ψ c)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_PointDerivations_exists_reader_tensor_linearMap_dual_of_linearEquiv_tensor.solution
