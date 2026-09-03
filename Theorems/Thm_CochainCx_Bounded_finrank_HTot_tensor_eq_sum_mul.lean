import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import P2M.Util
import P2M.Sol.S_CochainCx_Bounded_finrank_HTot_tensor_eq_sum_mul

set_option autoImplicit false

universe u

open TensorProduct

theorem CochainCx.Bounded.finrank_HTot_tensor_eq_sum_mul
    {k : Type u} [Field k] (C D : CochainCx.Bounded k)
    (hC : ∀ p, Module.Finite k (C.H p)) (hD : ∀ q, Module.Finite k (D.H q)) (n : ℕ) :
    Module.Finite k (DoubleComplex.HTot (C.tensor D) n) ∧
      Module.finrank k (DoubleComplex.HTot (C.tensor D) n) =
        ∑ i ∈ Finset.range (n + 1), C.hfinrank i * D.hfinrank (n - i) := by p2m_exact_reverting @_root_.P2MW.S_CochainCx_Bounded_finrank_HTot_tensor_eq_sum_mul.solution
