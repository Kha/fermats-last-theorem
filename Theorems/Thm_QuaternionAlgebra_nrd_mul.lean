import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_nrd_mul
open Quaternion QuaternionAlgebra
theorem QuaternionAlgebra.nrd_mul {R : Type*} [CommRing R] {a b : R}
    (x y : ℍ[R, a, b]) : QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_nrd_mul.solution
