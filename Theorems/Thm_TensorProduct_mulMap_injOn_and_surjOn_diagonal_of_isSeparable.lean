import Mathlib
import P2M.Util
import P2M.Sol.S_TensorProduct_mulMap_injOn_and_surjOn_diagonal_of_isSeparable

set_option autoImplicit false
open scoped TensorProduct

theorem TensorProduct.mulMap_injOn_and_surjOn_diagonal_of_isSeparable
    {F K P : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Algebra.IsSeparable F K]
    [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P]
    (π : K ⊗[F] P →ₗ[K] P) (hπ : ∀ (a : K) (v : P), π (a ⊗ₜ[F] v) = a • v) :
    (∀ w : K ⊗[F] P,
        (∀ k : K, k • w = LinearMap.baseChange K ((LinearMap.lsmul K P k).restrictScalars F) w) →
          π w = 0 → w = 0) ∧
      ∀ v : P, ∃ w : K ⊗[F] P,
        (∀ k : K, k • w = LinearMap.baseChange K ((LinearMap.lsmul K P k).restrictScalars F) w) ∧ π w = v := by p2m_exact_reverting @_root_.P2MW.S_TensorProduct_mulMap_injOn_and_surjOn_diagonal_of_isSeparable.solution
