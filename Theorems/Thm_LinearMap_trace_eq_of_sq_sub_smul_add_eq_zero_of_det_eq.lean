import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import P2M.Util
import P2M.Sol.S_LinearMap_trace_eq_of_sq_sub_smul_add_eq_zero_of_det_eq

theorem LinearMap.trace_eq_of_sq_sub_smul_add_eq_zero_of_det_eq
    {R : Type*} {M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2)
    (f : M →ₗ[R] M) (a d : R) (hf : f * f - a • f + d • (1 : M →ₗ[R] M) = 0)
    (hdet : LinearMap.det f = d) (hd : d ≠ 0) :
    LinearMap.trace R M f = a := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_trace_eq_of_sq_sub_smul_add_eq_zero_of_det_eq.solution
