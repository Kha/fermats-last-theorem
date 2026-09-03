import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import P2M.Util
import P2M.Sol.S_Module_End_trace_eq_of_mul_self_sub_smul_add_smul_eq_zero

theorem Module.End.trace_eq_of_mul_self_sub_smul_add_smul_eq_zero {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] (b : Module.Basis (Fin 2) k V) {f : Module.End k V} {a c : k} (hrel : f * f - a • f + c • 1 = 0) (hdet : LinearMap.det f = c) (hc : c ≠ 0) : LinearMap.trace k V f = a := by p2m_exact_reverting @_root_.P2MW.S_Module_End_trace_eq_of_mul_self_sub_smul_add_smul_eq_zero.solution
