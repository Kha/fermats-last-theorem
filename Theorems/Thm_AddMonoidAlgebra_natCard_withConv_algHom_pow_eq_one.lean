import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidAlgebra_natCard_withConv_algHom_pow_eq_one

set_option autoImplicit false

universe u v w

theorem AddMonoidAlgebra.natCard_withConv_algHom_pow_eq_one
    (k : Type u) [CommRing k] (M : Type v) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (A : Type w) [CommRing A] [Algebra k A]
    (m : ℕ) [NeZero m] [HasEnoughRootsOfUnity A m] :
    Nat.card {φ : WithConv (AddMonoidAlgebra k M →ₐ[k] A) // φ ^ m = 1} =
      m ^ Module.finrank ℤ M := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidAlgebra_natCard_withConv_algHom_pow_eq_one.solution
