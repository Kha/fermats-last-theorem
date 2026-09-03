import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_finrank_eq_finrank_subalgebra_mul_finrank_quotient_of_isNilpotent
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

universe u v

theorem HopfAlgebra.finrank_eq_finrank_subalgebra_mul_finrank_quotient_of_isNilpotent
    (k : Type u) [Field k] (H : Type v) [CommRing H] [HopfAlgebra k H] [Module.Finite k H]
    (hH : ∀ x : H, Coalgebra.counit (R := k) x = 0 → IsNilpotent x)
    (S : Subalgebra k H)
    (hΔ : ∀ x ∈ S, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : TensorProduct k H H | ∃ a ∈ S, ∃ b ∈ S, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ S, HopfAlgebra.antipode k x ∈ S) :
    Module.finrank k H =
      Module.finrank k S *
        Module.finrank k (H ⧸ Ideal.span {x : H | x ∈ S ∧ Coalgebra.counit (R := k) x = 0}) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_finrank_eq_finrank_subalgebra_mul_finrank_quotient_of_isNilpotent.solution
