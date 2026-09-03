import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import P2M.Util
import P2M.Sol.S_Submodule_finrank_pi_univ_eq_sum

open Module
theorem Submodule.finrank_pi_univ_eq_sum
    {k : Type*} [Field k] {ι : Type*} [Fintype ι] {Φ : ι → Type*}
    [∀ v, AddCommGroup (Φ v)] [∀ v, Module k (Φ v)]
    (L : ∀ v, Submodule k (Φ v)) [∀ v, FiniteDimensional k (L v)] :
    finrank k (Submodule.pi Set.univ L) = ∑ v, finrank k (L v) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_finrank_pi_univ_eq_sum.solution
