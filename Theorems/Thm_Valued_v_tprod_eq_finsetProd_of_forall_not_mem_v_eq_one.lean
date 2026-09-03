import Mathlib
import P2M.Util
import P2M.Sol.S_Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one

set_option autoImplicit false

open scoped Topology

theorem Valued.v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {ι : Type*} (f : ι → K) (hf : Multipliable f)
    (S : Finset ι) (hS : ∀ i, i ∉ S → Valued.v (f i) = 1) :
    Valued.v (∏' i, f i) = ∏ i ∈ S, Valued.v (f i) := by p2m_exact_reverting @_root_.P2MW.S_Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one.solution
