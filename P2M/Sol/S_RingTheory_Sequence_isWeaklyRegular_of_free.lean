import Mathlib
import Theorems.Thm_RingTheory_Sequence_isWeaklyRegular_of_free_aux
import P2M.Util
namespace P2MW.S_RingTheory_Sequence_isWeaklyRegular_of_free

open scoped Pointwise TensorProduct

theorem solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Nontrivial M] {s : List R} :
    RingTheory.Sequence.IsWeaklyRegular M s ↔ RingTheory.Sequence.IsWeaklyRegular R s := by
  let b := Module.Free.chooseBasis R M
  have : Nontrivial R := Module.nontrivial R M
  rw [b.repr.isWeaklyRegular_congr, RingTheory.Sequence.isWeaklyRegular_of_free_aux]
