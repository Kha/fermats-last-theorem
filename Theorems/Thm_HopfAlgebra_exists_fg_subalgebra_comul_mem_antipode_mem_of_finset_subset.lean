import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    (s : Finset H) (hs : (↑s : Set H) ⊆ K) :
    ∃ K₀ : Subalgebra k H, K₀ ≤ K ∧ K₀.FG ∧ (↑s : Set H) ⊆ K₀ ∧
      (∀ x ∈ K₀, Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K₀, ∃ b ∈ K₀, t = a ⊗ₜ[k] b}) ∧
      (∀ x ∈ K₀, HopfAlgebra.antipode k x ∈ K₀) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset.solution
