import Mathlib.RingTheory.Regular.RegularSequence
import P2M.Util
import P2M.Sol.S_RingTheory_Sequence_isWeaklyRegular_ofFn_of_isWeaklyRegular_ofFn_of_forall_mem_span

universe u v
theorem RingTheory.Sequence.isWeaklyRegular_ofFn_of_isWeaklyRegular_ofFn_of_forall_mem_span
    {P : Type u} [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    {M : Type v} [AddCommGroup M] [Module P M] [Module.Finite P M]
    {n : ℕ} (f y : Fin n → P)
    (hy : RingTheory.Sequence.IsWeaklyRegular M (List.ofFn y))
    (hyf : ∀ k, y k ∈ Ideal.span (Set.range f))
    (hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal P) :
    RingTheory.Sequence.IsWeaklyRegular M (List.ofFn f) := by p2m_exact_reverting @_root_.P2MW.S_RingTheory_Sequence_isWeaklyRegular_ofFn_of_isWeaklyRegular_ofFn_of_forall_mem_span.solution
