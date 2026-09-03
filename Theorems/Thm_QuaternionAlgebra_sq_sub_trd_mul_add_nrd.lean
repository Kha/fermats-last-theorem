import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_sq_sub_trd_mul_add_nrd
open Quaternion QuaternionAlgebra
theorem QuaternionAlgebra.sq_sub_trd_mul_add_nrd {R : Type*} [CommRing R] {a b : R}
    (x : ℍ[R, a, b]) :
    x * x - ((QuaternionAlgebra.trd x : R) : ℍ[R, a, b]) * x + ((QuaternionAlgebra.nrd x : R) : ℍ[R, a, b]) = 0 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_sq_sub_trd_mul_add_nrd.solution
