import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_forall_withConv_pow_eq_one_of_forall_algHom_pow_eq_one_of_isAlgClosed

set_option autoImplicit false

theorem HopfAlgebra.forall_withConv_pow_eq_one_of_forall_algHom_pow_eq_one_of_isAlgClosed
    (R : Type) [CommRing R] [IsDomain R] (H : Type) [CommRing H] [HopfAlgebra R H]
    [Module.Finite R H] [Module.Flat R H]
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L]
    (hRL : Function.Injective (algebraMap R L))
    (m : ℕ) (hL : ∀ f : WithConv (H →ₐ[R] L), f ^ m = 1)
    (T : Type) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)) : f ^ m = 1 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_forall_withConv_pow_eq_one_of_forall_algHom_pow_eq_one_of_isAlgClosed.solution
