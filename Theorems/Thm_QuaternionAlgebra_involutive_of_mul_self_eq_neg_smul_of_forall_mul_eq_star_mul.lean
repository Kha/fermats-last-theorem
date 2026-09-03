import Mathlib
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_involutive_of_mul_self_eq_neg_smul_of_forall_mul_eq_star_mul

set_option autoImplicit false

open QuaternionAlgebra
open scoped Quaternion

universe u v

theorem QuaternionAlgebra.involutive_of_mul_self_eq_neg_smul_of_forall_mul_eq_star_mul
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {a b c : R} (hc : 0 < c)
    (t : ℍ[R, a, b]) (ht : t * t = (-c) • (1 : ℍ[R, a, b]))
    {I : Type v} (e : I → ℍ[R, a, b]) (he : Function.Injective e)
    (σ : I → I) (hσ : ∀ d : I, t * e (σ d) = star (e d) * t) :
    Function.Involutive σ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_involutive_of_mul_self_eq_neg_smul_of_forall_mul_eq_star_mul.solution
