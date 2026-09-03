import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_TwistedCommutant
import P2M.Util
import P2M.Sol.S_Algebra_trace_tensorProduct_rightActions_tmul_eq_algebraMap_trace_mul

set_option autoImplicit false

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal Topology

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem Algebra.trace_tensorProduct_rightActions_tmul_eq_algebraMap_trace_mul
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] (l : L) (a : A) :
    Algebra.trace A (L ⊗[K] A) (l ⊗ₜ[K] a) = algebraMap K A (Algebra.trace K L l) * a := by p2m_exact_reverting @_root_.P2MW.S_Algebra_trace_tensorProduct_rightActions_tmul_eq_algebraMap_trace_mul.solution
