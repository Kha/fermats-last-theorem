import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_norm_one_tmul_eq_algebraMap_norm

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem Algebra.norm_one_tmul_eq_algebraMap_norm
    {K : Type u} [CommRing K] {L : Type v} [Ring L] [Algebra K L] [Module.Free K L] [Module.Finite K L]
    (K' : Type w) [CommRing K'] [Algebra K K'] (x : L) :
    Algebra.norm K' ((1 : K') ⊗ₜ[K] x : K' ⊗[K] L) = algebraMap K K' (Algebra.norm K x) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_norm_one_tmul_eq_algebraMap_norm.solution
