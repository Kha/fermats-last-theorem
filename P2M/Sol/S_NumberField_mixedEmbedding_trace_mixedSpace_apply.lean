import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.Complex
import P2M.Util
namespace P2MW.S_NumberField_mixedEmbedding_trace_mixedSpace_apply

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding

namespace Ws1
namespace K5b2

theorem trace_pi_self (k : Type*) [Field k] (ι : Type*) [Fintype ι] [DecidableEq ι] (z : ι → k) :
    Algebra.trace k (ι → k) z = ∑ i, z i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun k ι), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_repr, Pi.basisFun_apply, Pi.mul_apply,
    Pi.single_eq_same, mul_one]

end Ws1.K5b2

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K] (z : mixedSpace K) :
    Algebra.trace ℝ (mixedSpace K) z =
      (∑ w : {w : InfinitePlace K // w.IsReal}, z.1 w) +
        ∑ w : {w : InfinitePlace K // w.IsComplex}, 2 * (z.2 w).re := by
  classical
  rw [Algebra.trace_prod_apply, Ws1.K5b2.trace_pi_self]
  congr 1
  rw [← Algebra.trace_trace (S := ℂ), Ws1.K5b2.trace_pi_self, Algebra.trace_complex_apply, Complex.re_sum,
    Finset.mul_sum]
