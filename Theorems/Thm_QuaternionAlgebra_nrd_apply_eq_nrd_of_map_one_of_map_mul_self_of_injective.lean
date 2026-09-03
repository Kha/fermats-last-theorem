import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_nrd_apply_eq_nrd_of_map_one_of_map_mul_self_of_injective

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.nrd_apply_eq_nrd_of_map_one_of_map_mul_self_of_injective
    {K : Type} [Field K] {a b a' b' : K}
    (η : ℍ[K, a, b] →ₗ[K] ℍ[K, a', b']) (h1 : η 1 = 1) (hη : Function.Injective η)
    (hsq : ∀ x : ℍ[K, a, b], η (x * x) = η x * η x) (x : ℍ[K, a, b]) :
    QuaternionAlgebra.nrd (η x) = QuaternionAlgebra.nrd x := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_nrd_apply_eq_nrd_of_map_one_of_map_mul_self_of_injective.solution
