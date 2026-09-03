import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.free_subalgebra_of_isNilpotent_ker_counit
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    (hnil : IsNilpotent (RingHom.ker ((Bialgebra.counitAlgHom k H).comp K.val))) :
    Module.Free ↥K H := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit.solution
