import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_levelLifts_pi_of_forall_exists_levelLifts
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_levelLifts_pi_of_forall_exists_levelLifts
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)]
    {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {m : ℕ} (Rp : Fin m → Type) [∀ p, CommRing (Rp p)] (φ : ∀ p, S →+* Rp p) (ζ : ∀ p, (Rp p)ˣ)
    (hL : ∀ p : Fin m,
      ∃ (lift : ((i : Fin g) → ZMod (δ i)) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (φ p))))
        (dualLift : (((i : Fin g) → ZMod (δ i)) →+ ZMod d) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (φ p)))),
        lift 0 = 1 ∧ (∀ h h' : ((i : Fin g) → ZMod (δ i)), lift (h + h') = lift h * lift h') ∧
        dualLift 0 = 1 ∧ (∀ c c' : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, dualLift (c + c') = dualLift c * dualLift c') ∧
        (∀ (c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d) (h : ((i : Fin g) → ZMod (δ i))),
          dualLift c * lift h = ThetaPt.ofScalar (ζ p ^ (c h).val) * (lift h * dualLift c))) :
    ∃ (lift : ((i : Fin g) → ZMod (δ i)) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (RingHom.pi φ))))
        (dualLift : (((i : Fin g) → ZMod (δ i)) →+ ZMod d) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (RingHom.pi φ)))),
        lift 0 = 1 ∧ (∀ h h' : ((i : Fin g) → ZMod (δ i)), lift (h + h') = lift h * lift h') ∧
        dualLift 0 = 1 ∧ (∀ c c' : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, dualLift (c + c') = dualLift c * dualLift c') ∧
        (∀ (c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d) (h : ((i : Fin g) → ZMod (δ i))),
          dualLift c * lift h = ThetaPt.ofScalar (MulEquiv.piUnits.symm ζ ^ (c h).val) * (lift h * dualLift c)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_levelLifts_pi_of_forall_exists_levelLifts.solution
