import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle

set_option autoImplicit false

universe u v w

theorem Algebra.FormallySmooth.exists_linearMap_eq_of_symmetric_hochschild_two_cocycle
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (ψ : S →ₗ[R] S →ₗ[R] M)
    (hsymm : ∀ x y, ψ x y = ψ y x)
    (hone : ∀ y, ψ 1 y = 0)
    (hcoc : ∀ x y z, x • ψ y z - ψ (x * y) z + ψ x (y * z) - z • ψ x y = 0) :
    ∃ l : S →ₗ[R] M, l 1 = 0 ∧ ∀ x y, ψ x y = l (x * y) - x • l y - y • l x := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle.solution
