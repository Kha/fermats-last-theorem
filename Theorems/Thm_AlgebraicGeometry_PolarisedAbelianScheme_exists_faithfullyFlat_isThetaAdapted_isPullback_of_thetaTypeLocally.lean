import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_isThetaAdapted_isPullback_of_thetaTypeLocally
attribute [-instance] AlgebraicGeometry.ThetaLevel.Heis.instInv AlgebraicGeometry.ThetaLevel.Heis.Gam.instFinite AlgebraicGeometry.ThetaLevel.Heis.instMul AlgebraicGeometry.ThetaLevel.Heis.Gam.instFintype AlgebraicGeometry.ThetaLevel.Heis.instGroup AlgebraicGeometry.ThetaLevel.Heis.instDecidableEq AlgebraicGeometry.ThetaLevel.Heis.instOne AlgebraicGeometry.ThetaLevel.Heis.instFintype
attribute [-simp] AlgebraicGeometry.ThetaLevel.Heis.theta_h AlgebraicGeometry.ThetaLevel.Heis.mk.injEq AlgebraicGeometry.ThetaLevel.Heis.one_k AlgebraicGeometry.ThetaLevel.Heis.mk.sizeOf_spec AlgebraicGeometry.ThetaLevel.Heis.mul_a AlgebraicGeometry.ThetaLevel.Heis.eta_a AlgebraicGeometry.ThetaLevel.Heis.mul_h AlgebraicGeometry.ThetaLevel.Heis.inv_k AlgebraicGeometry.ThetaLevel.Heis.mul_k AlgebraicGeometry.ThetaLevel.Heis.one_a AlgebraicGeometry.ThetaLevel.Heis.cen_a AlgebraicGeometry.ThetaLevel.Heis.one_h AlgebraicGeometry.ThetaLevel.Heis.theta_k AlgebraicGeometry.ThetaLevel.Heis.cen_k AlgebraicGeometry.ThetaLevel.Heis.theta_a AlgebraicGeometry.ThetaLevel.Heis.inv_h AlgebraicGeometry.ThetaLevel.diagOp_apply AlgebraicGeometry.ThetaLevel.Heis.cen_h AlgebraicGeometry.ThetaLevel.Heis.eta_h AlgebraicGeometry.ThetaLevel.shiftOp_apply AlgebraicGeometry.ThetaLevel.Heis.inv_a AlgebraicGeometry.ThetaLevel.Heis.eta_k AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_faithfullyFlat_isThetaAdapted_isPullback_of_thetaTypeLocally
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u : PolarisedAbelianScheme g (N + 1) n S) (hu : PolarisedAbelianScheme.ThetaTypeLocally δ S u) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'), Module.FaithfullyFlat S S' ∧
      ∃ X' : FramedPolarisedAbelianScheme g N n S', X'.IsThetaAdapted δ e ∧
        PolarisedAbelianScheme.IsPullback (algebraMap S S') u X'.toPolarisedAbelianScheme := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_isThetaAdapted_isPullback_of_thetaTypeLocally.solution
