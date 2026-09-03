import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.FiniteLength
import Mathlib.LinearAlgebra.FreeModule.Basic
import P2M.Util
import P2M.Sol.S_Module_free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal

universe u v
theorem Module.free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (xs : List R) (hxs : RingTheory.Sequence.IsRegular R xs)
    (hspan : Ideal.ofList xs = IsLocalRing.maximalIdeal R)
    (s : List R) (hs : ∀ r ∈ s, r ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular M s) (hlen : s.length = xs.length)
    (hfl : IsFiniteLength R (M ⧸ (Ideal.ofList s • ⊤ : Submodule R M))) :
    Module.Free R M := by p2m_exact_reverting @_root_.P2MW.S_Module_free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal.solution
