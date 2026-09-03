import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero

set_option autoImplicit false

theorem Module.End.isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero
    {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type*} (t : ι → Module.End K V) (ht : ∀ i j, Commute (t i) (t j))
    (a : Module.End K V) (ha : a ∈ Algebra.adjoin K (Set.range t))
    (h : ∀ (χ : ι → K) (v : V), v ≠ 0 → (∀ i, t i v = χ i • v) → a v = 0) :
    IsNilpotent a := by p2m_exact_reverting @_root_.P2MW.S_Module_End_isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero.solution
