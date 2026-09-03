import Mathlib
import P2M.Util
import P2M.Sol.S_RingTheory_Sequence_isWeaklyRegular_of_free

open scoped Pointwise TensorProduct
theorem RingTheory.Sequence.isWeaklyRegular_of_free {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Nontrivial M] {s : List R} :
    RingTheory.Sequence.IsWeaklyRegular M s ↔ RingTheory.Sequence.IsWeaklyRegular R s := by p2m_exact_reverting @_root_.P2MW.S_RingTheory_Sequence_isWeaklyRegular_of_free.solution
