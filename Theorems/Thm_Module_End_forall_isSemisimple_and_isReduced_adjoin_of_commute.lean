import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_forall_isSemisimple_and_isReduced_adjoin_of_commute

set_option autoImplicit false

theorem Module.End.forall_isSemisimple_and_isReduced_adjoin_of_commute
    {K : Type*} [Field K] [PerfectField K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {s : Set (Module.End K V)} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (hs : ∀ x ∈ s, Module.End.IsSemisimple x) :
    (∀ a ∈ Algebra.adjoin K s, Module.End.IsSemisimple a) ∧ IsReduced ↥(Algebra.adjoin K s) := by p2m_exact_reverting @_root_.P2MW.S_Module_End_forall_isSemisimple_and_isReduced_adjoin_of_commute.solution
