import Mathlib
import P2M.Util
import P2M.Sol.S_Valued_multipliable_one_add_of_tendsto_cofinite_zero

set_option autoImplicit false

open Filter Topology

theorem Valued.multipliable_one_add_of_tendsto_cofinite_zero
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    {ι : Type*} (f : ι → K) (hf : Tendsto f cofinite (𝓝 0)) :
    Multipliable (fun i => 1 + f i) := by p2m_exact_reverting @_root_.P2MW.S_Valued_multipliable_one_add_of_tendsto_cofinite_zero.solution
