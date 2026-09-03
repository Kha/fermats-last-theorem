import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_bijective_and_flip_bijective_of_baseChange_residueField

universe u v w₁ w₂ w₁' w₂'

open scoped TensorProduct

theorem LinearMap.bijective_and_flip_bijective_of_baseChange_residueField
    {R : Type u} [CommRing R] [IsLocalRing R] {k : Type v} [Field k] [Algebra R k]
    {M : Type w₁} {N : Type w₂} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {Mk : Type w₁'} {Nk : Type w₂'} [AddCommGroup Mk] [Module k Mk] [AddCommGroup Nk] [Module k Nk]
    [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N]
    (hπ : Function.Surjective (algebraMap R k))
    (B : M →ₗ[R] N →ₗ[R] R) (Bk : Mk →ₗ[k] Nk →ₗ[k] k)
    (eM : k ⊗[R] M ≃ₗ[k] Mk) (eN : k ⊗[R] N ≃ₗ[k] Nk)
    (hcomp : ∀ m n, Bk (eM (1 ⊗ₜ[R] m)) (eN (1 ⊗ₜ[R] n)) = algebraMap R k (B m n))
    (hBk : Function.Bijective Bk ∧ Function.Bijective Bk.flip) :
    Function.Bijective B ∧ Function.Bijective B.flip := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_bijective_and_flip_bijective_of_baseChange_residueField.solution
