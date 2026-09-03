import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import P2M.Util
import P2M.Sol.S_LinearMap_charpoly_eq_X_sub_one_sq_of_sub_one_mul_self_eq_zero

universe u v
theorem LinearMap.charpoly_eq_X_sub_one_sq_of_sub_one_mul_self_eq_zero {A : Type u} [CommRing A]
    [IsDomain A] {V : Type v} [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]
    (hV : Module.finrank A V = 2) (f : Module.End A V) (hf : (f - 1) * (f - 1) = 0) :
    LinearMap.charpoly f = (Polynomial.X - 1) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_charpoly_eq_X_sub_one_sq_of_sub_one_mul_self_eq_zero.solution
