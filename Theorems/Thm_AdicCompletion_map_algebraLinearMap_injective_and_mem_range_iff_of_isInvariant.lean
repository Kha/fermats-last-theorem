import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant

set_option autoImplicit false

theorem AdicCompletion.map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant
    {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {S : Type*} [CommRing S] [Algebra A S] [Module.Finite A S] [FaithfulSMul A S]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G A S]
    [Algebra.IsInvariant A S G] :
    Function.Injective (AdicCompletion.map I (Algebra.linearMap A S)) ∧
    ∀ x : AdicCompletion I S,
      x ∈ LinearMap.range (AdicCompletion.map I (Algebra.linearMap A S)) ↔
        ∀ g : G, AdicCompletion.map I (DistribSMul.toLinearMap A S g) x = x := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant.solution
