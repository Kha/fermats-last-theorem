import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField
    {k : Type u} [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (hred : ∀ K' : Subalgebra k H,
      (∀ x ∈ K', Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b}) →
      (∀ x ∈ K', HopfAlgebra.antipode k x ∈ K') → K'.FG → IsReduced ↥K' →
      Module.FaithfullyFlat ↥K' H)
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) (hfg : K.FG) :
    Module.FaithfullyFlat ↥K H := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField.solution
