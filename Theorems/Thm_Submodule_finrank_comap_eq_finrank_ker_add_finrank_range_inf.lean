import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import P2M.Util
import P2M.Sol.S_Submodule_finrank_comap_eq_finrank_ker_add_finrank_range_inf

open Module
theorem Submodule.finrank_comap_eq_finrank_ker_add_finrank_range_inf
    {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (N : Submodule k W) [FiniteDimensional k (N.comap f)] :
    finrank k (N.comap f)
      = finrank k (LinearMap.ker f) + finrank k (LinearMap.range f ⊓ N : Submodule k W) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_finrank_comap_eq_finrank_ker_add_finrank_range_inf.solution
