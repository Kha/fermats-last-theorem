import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_point_toAlgHom_eq_comp_of_etale_cartierDual_of_forall_comp_eq_of_reduction_pow_eq_frobenius_conv_verschiebung
attribute [-instance] CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient Deformation.TruncWitt.instSubsingleton Deformation.DieudonneModule.instInhabited Deformation.wittHomShiftLE_directedSystem Deformation.DieudonneModule.instAddCommGroup HopfAlgebra.IsHopfTower.refl
attribute [-simp] HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec Deformation.wittHomDieudonneDatum_F_apply Deformation.TruncWitt.shift_truncate Deformation.coe_wittHomShift Deformation.coe_wittHomFrobenius Deformation.wittHomDieudonneDatum_V_apply Deformation.TruncWitt.coeff_map Deformation.coe_wittHomVerschiebung
attribute [-simp] Deformation.coe_wittHomRestrict Deformation.coe_wittHomMap Deformation.TruncWitt.map_truncate Deformation.TruncWitt.coeff_frobeniusFun Deformation.TruncWitt.verschiebung_truncate Deformation.TruncWitt.map_id Deformation.TruncWitt.shiftLE_refl Deformation.DieudonneModule.dieudonneDatum_F_apply Deformation.coe_wittHomShiftLE Deformation.DieudonneModule.frobenius_of Deformation.DieudonneModule.lift_of Deformation.TruncWitt.verschiebungIter_apply Deformation.DieudonneModule.map_of Deformation.DieudonneModule.dieudonneDatum_V_apply Deformation.DieudonneModule.of_shift Deformation.TruncWitt.shiftLE_truncate Deformation.DieudonneModule.verschiebung_of Deformation.DieudonneModule.of_shiftLE Deformation.wittHomShiftLE_refl HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.exists_point_toAlgHom_eq_comp_of_etale_cartierDual_of_forall_comp_eq_of_reduction_pow_eq_frobenius_conv_verschiebung
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsDomain O] [HenselianLocalRing O]
    [Algebra O (AlgebraicClosure ℚ)] [Algebra O (ZMod p)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (hres : ∀ x : O, algebraMap O (ZMod p) x = 0 ↔
      P.valuation (algebraMap O (AlgebraicClosure ℚ) x) < 1)
    {h : ℕ} (H : PDivisibleGroup O p h)

    (u ε w : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (hu : ∀ v : ℕ, (H.transition v).comp (u (v + 1)) = (u v).comp (H.transition v))
    (hεε : ∀ v : ℕ, (ε v).comp (ε v) = ε v)
    (hεtr : ∀ v : ℕ, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))
    (hεu : ∀ v : ℕ, (ε v).comp (u v) = (u v).comp (ε v))
    (hwtr : ∀ v : ℕ, (H.transition v).comp (w (v + 1)) = (w v).comp (H.transition v))
    (hεw : ∀ v : ℕ, (ε v).comp (w v) = w v) (hwε : ∀ v : ℕ, (w v).comp (ε v) = w v)
    (hwuε : ∀ v : ℕ, (w v).comp ((u v).comp (ε v)) = ε v)
    (huεw : ∀ v : ℕ, ((u v).comp (ε v)).comp (w v) = ε v)

    (hFV : ∀ Fk : ZMod p ⊗[O] H.level 1 →ₐc[ZMod p] ZMod p ⊗[O] H.level 1, (∀ x, Fk x = x ^ p) →
      ∀ FD : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₐ[ZMod p]
          CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1), (∀ ψ, FD ψ = ψ ^ p) →
      ∃ (n : ℕ) (a b : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₐc[ZMod p]
          CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)),
        (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u 1)) :
            CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
              CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)) ^ n =
          (WithConv.toConv ((FD : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)) ∘ₗ
              (a : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1))) *
            WithConv.toConv ((b : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)) ∘ₗ
              (CartierDual.map Fk : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)))).ofConv)
    (v : ℕ)

    (Mt : Type) [CommRing Mt] [HopfAlgebra O Mt] [Coalgebra.IsCocomm O Mt] [Module.Free O Mt] [Module.Finite O Mt]
    [Algebra.Etale O (CartierDual O Mt)]
    (π : H.level v →ₐc[O] Mt) (hπ : Function.Surjective π)
    (huniv : ∀ (M' : Type) [CommRing M'] [HopfAlgebra O M'] [Coalgebra.IsCocomm O M']
        [Module.Free O M'] [Module.Finite O M'] [Algebra.Etale O (CartierDual O M')]
        (f : H.level v →ₐc[O] M'), ∃! g : Mt →ₐc[O] M', g.comp π = f) :
    ∀ f : H.Point (AlgebraicClosure ℚ) v,
      (∀ a : H.level v, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (PDivisibleGroup.Point.toAlgHom f).comp (ε v : H.level v →ₐ[O] H.level v) =
        PDivisibleGroup.Point.toAlgHom f →
      ∃ g : Mt →ₐ[O] AlgebraicClosure ℚ,
        PDivisibleGroup.Point.toAlgHom f = g.comp (π : H.level v →ₐ[O] Mt) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_point_toAlgHom_eq_comp_of_etale_cartierDual_of_forall_comp_eq_of_reduction_pow_eq_frobenius_conv_verschiebung.solution
