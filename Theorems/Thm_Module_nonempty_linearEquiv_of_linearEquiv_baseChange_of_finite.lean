import Mathlib
import P2M.Util
import P2M.Sol.S_Module_nonempty_linearEquiv_of_linearEquiv_baseChange_of_finite

set_option autoImplicit false

open scoped TensorProduct

theorem Module.nonempty_linearEquiv_of_linearEquiv_baseChange_of_finite
    (K : Type*) [Field K] [Finite K] (L : Type*) [CommRing L] [Nontrivial L] [Algebra K L]
    (A : Type*) [Ring A] [Algebra K A]
    (M N : Type*) [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
    [Module.Finite K M]
    [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N] [Module.Finite K N]
    (e : L ⊗[K] M ≃ₗ[L] L ⊗[K] N)
    (he : ∀ (a : A) (x : L ⊗[K] M),
      e ((DistribSMul.toLinearMap K M a).baseChange L x) =
        (DistribSMul.toLinearMap K N a).baseChange L (e x)) :
    Nonempty (M ≃ₗ[A] N) := by p2m_exact_reverting @_root_.P2MW.S_Module_nonempty_linearEquiv_of_linearEquiv_baseChange_of_finite.solution
