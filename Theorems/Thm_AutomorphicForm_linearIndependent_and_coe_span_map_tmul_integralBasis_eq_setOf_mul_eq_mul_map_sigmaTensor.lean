import Definitions.Def_AutomorphicForm_TwistedCommutant
import P2M.Util
import P2M.Sol.S_AutomorphicForm_linearIndependent_and_coe_span_map_tmul_integralBasis_eq_setOf_mul_eq_mul_map_sigmaTensor

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.linearIndependent_and_coe_span_map_tmul_integralBasis_eq_setOf_mul_eq_mul_map_sigmaTensor
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    {κ : Type} [Fintype κ] (x : κ → Matrix (Fin 2) (Fin 2) L) (hx : LinearIndependent K x)
    (hspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range x)) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    LinearIndependent ℝ (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × κ =>
        (x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (integralBasis K p.1))) ∧
    (Submodule.span ℝ (Set.range (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × κ =>
        (x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (integralBasis K p.1)))) :
        Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
      {X | X * ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] InfiniteAdeleRing K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
        ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] InfiniteAdeleRing K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_linearIndependent_and_coe_span_map_tmul_integralBasis_eq_setOf_mul_eq_mul_map_sigmaTensor.solution
