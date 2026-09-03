import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_pDivisibleGroup_bialgHom_injective_range_eq_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.exists_pDivisibleGroup_bialgHom_injective_range_eq_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
    {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (p : ℕ) [Fact p.Prime] {h t : ℕ} (G : PDivisibleGroup R p h) (T : PDivisibleGroup R p t)
    (π : ∀ v : ℕ, G.level v →ₐc[R] T.level v) (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v : ℕ, (T.transition v).comp (π (v + 1)) = (π v).comp (G.transition v)) :
    ∃ (hB : ℕ) (B : PDivisibleGroup R p hB) (j : ∀ v : ℕ, B.level v →ₐc[R] G.level v),
      h = t + hB ∧
      (∀ v, Function.Injective (j v)) ∧
      (∀ v, (j v : B.level v →ₐ[R] G.level v).range = HopfAlgebra.hopfKer (π v)) ∧
      (∀ v : ℕ, (G.transition v).comp (j (v + 1)) = (j v).comp (B.transition v)) ∧

      (∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra R L] (v : ℕ) (x : G.Point L v),
        PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (j v : B.level v →ₐ[R] G.level v)) =
            (1 : B.Point L v) ↔
          ∃ y : T.Point L v,
            PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (π v : G.level v →ₐ[R] T.level v)) = x) ∧

      (∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra R L] (v : ℕ) (b : B.Point L v), ∃ x : G.Point L v,
        PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (j v : B.level v →ₐ[R] G.level v)) = b) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_bialgHom_injective_range_eq_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing.solution
