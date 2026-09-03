import Mathlib
import P2M.Util
import P2M.Sol.S_exteriorPower_exists_linearEquiv_baseChange

open scoped TensorProduct

theorem exteriorPower.exists_linearEquiv_baseChange
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    ∃ e : A ⊗[R] (⋀[R]^n M) ≃ₗ[A] ⋀[A]^n (A ⊗[R] M),
      ∀ (a : A) (m : Fin n → M),
        e (a ⊗ₜ exteriorPower.ιMulti R n m) =
          a • exteriorPower.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] m i) := by p2m_exact_reverting @_root_.P2MW.S_exteriorPower_exists_linearEquiv_baseChange.solution
