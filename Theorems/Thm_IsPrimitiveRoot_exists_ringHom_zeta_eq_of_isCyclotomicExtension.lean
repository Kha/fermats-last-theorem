import Mathlib
import P2M.Util
import P2M.Sol.S_IsPrimitiveRoot_exists_ringHom_zeta_eq_of_isCyclotomicExtension

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsPrimitiveRoot.exists_ringHom_zeta_eq_of_isCyclotomicExtension
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [Algebra ℚ K] [IsCyclotomicExtension {n} ℚ K]
    (L : Type*) [Field L] [CharZero L] (ξ : L) (hξ : IsPrimitiveRoot ξ n) :
    ∃ φ : K →+* L, φ (IsCyclotomicExtension.zeta n ℚ K) = ξ := by p2m_exact_reverting @_root_.P2MW.S_IsPrimitiveRoot_exists_ringHom_zeta_eq_of_isCyclotomicExtension.solution
