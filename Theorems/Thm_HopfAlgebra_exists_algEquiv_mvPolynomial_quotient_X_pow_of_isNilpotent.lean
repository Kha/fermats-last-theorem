import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_algEquiv_mvPolynomial_quotient_X_pow_of_isNilpotent
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

universe u v

theorem HopfAlgebra.exists_algEquiv_mvPolynomial_quotient_X_pow_of_isNilpotent
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : Type v) [CommRing H] [HopfAlgebra k H] [Module.Finite k H]
    (hH : ∀ x : H, Coalgebra.counit (R := k) x = 0 → IsNilpotent x) :
    ∃ (d : ℕ) (e : Fin d → ℕ), Nonempty (H ≃ₐ[k] (MvPolynomial (Fin d) k ⧸
      Ideal.span (Set.range fun i : Fin d => (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ p ^ (e i + 1)))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_algEquiv_mvPolynomial_quotient_X_pow_of_isNilpotent.solution
