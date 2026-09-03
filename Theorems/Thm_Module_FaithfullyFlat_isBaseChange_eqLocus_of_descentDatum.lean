import Mathlib
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_isBaseChange_eqLocus_of_descentDatum

universe u v w
theorem Module.FaithfullyFlat.isBaseChange_eqLocus_of_descentDatum
    {A : Type u} [CommRing A] (B : Type v) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (φ : TensorProduct A N B ≃ₗ[A] TensorProduct A B N)
    (hφ₁ : ∀ (b : B) (x : TensorProduct A N B), φ (b • x) = b • φ x)
    (hφ₂ : ∀ (b : B) (x : TensorProduct A N B),
      φ ((LinearMap.mulLeft A b).lTensor N x) = (DistribSMul.toLinearMap A N b).lTensor B (φ x))
    (hcocycle :
      (φ : TensorProduct A N B →ₗ[A] TensorProduct A B N).lTensor B ∘ₗ
          (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
          (φ : TensorProduct A N B →ₗ[A] TensorProduct A B N).rTensor B =
        (TensorProduct.comm A N B).toLinearMap.lTensor B ∘ₗ
          (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
          (φ : TensorProduct A N B →ₗ[A] TensorProduct A B N).rTensor B ∘ₗ
          (TensorProduct.assoc A N B B).symm.toLinearMap ∘ₗ
          (TensorProduct.comm A B B).toLinearMap.lTensor N ∘ₗ
          (TensorProduct.assoc A N B B).toLinearMap) :
    IsBaseChange B (LinearMap.eqLocus
        ((φ : TensorProduct A N B →ₗ[A] TensorProduct A B N) ∘ₗ (TensorProduct.mk A N B).flip 1)
        (TensorProduct.mk A B N 1)).subtype ∧
      ∀ (b b' : B) (m : N), φ (m ⊗ₜ[A] 1) = 1 ⊗ₜ[A] m →
        φ ((b • m) ⊗ₜ[A] b') = b ⊗ₜ[A] (b' • m) := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_isBaseChange_eqLocus_of_descentDatum.solution
