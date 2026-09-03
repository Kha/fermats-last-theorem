import Mathlib
import P2M.Util
import P2M.Sol.S_IsAlgebraic_mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem IsAlgebraic.mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed
    (K : Type) [Field K] [CharZero K]
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (h : IsDomain (K ⊗[ℚ] C))
    (x : K) (hx : IsAlgebraic ℚ x) :
    x ∈ Set.range (algebraMap ℚ K) := by p2m_exact_reverting @_root_.P2MW.S_IsAlgebraic_mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed.solution
