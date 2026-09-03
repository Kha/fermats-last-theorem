import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem Subalgebra.faithfullyFlat_of_faithfullyFlat_range_baseChange
    {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H] (K : Subalgebra k H)
    (k' : Type w) [Field k'] [Algebra k k']
    (hff : Module.FaithfullyFlat
      ↥((Algebra.TensorProduct.map (AlgHom.id k' k') K.val).range) (k' ⊗[k] H)) :
    Module.FaithfullyFlat ↥K H := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange.solution
