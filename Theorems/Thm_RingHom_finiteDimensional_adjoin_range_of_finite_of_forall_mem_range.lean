import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range

theorem RingHom.finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
    {R S E K : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Field E] [Field K] [Algebra E K]
    (χ' : S →+* K) (h : ∀ r : R, χ' (algebraMap R S r) ∈ (algebraMap E K).range) :
    FiniteDimensional E (IntermediateField.adjoin E (Set.range χ')) := by p2m_exact_reverting @_root_.P2MW.S_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range.solution
