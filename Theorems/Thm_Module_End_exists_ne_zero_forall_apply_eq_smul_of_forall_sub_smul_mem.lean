import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import P2M.Util
import P2M.Sol.S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem
set_option autoImplicit false

theorem Module.End.exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type*} (T : ι → Module.End K V) (hT : ∀ i j, Commute (T i) (T j))
    (W : Submodule K V) (hW : ∀ i, ∀ w ∈ W, T i w ∈ W)
    (mu : ι → K) (v : V) (hv : v ∉ W) (heig : ∀ i, T i v - mu i • v ∈ W) :
    ∃ u : V, u ≠ 0 ∧ ∀ i, T i u = mu i • u := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem.solution
