import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem Subalgebra.faithfullyFlat_of_directed_of_forall_faithfullyFlat
    {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H] (K : Subalgebra k H)
    {ι : Type w} [Nonempty ι] (F : ι → Subalgebra k H) (hdir : Directed (· ≤ ·) F)
    (hle : ∀ i, F i ≤ K) (hcov : ∀ x ∈ K, ∃ i, x ∈ F i)
    (hff : ∀ i, Module.FaithfullyFlat ↥(F i) H) :
    Module.FaithfullyFlat ↥K H := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat.solution
