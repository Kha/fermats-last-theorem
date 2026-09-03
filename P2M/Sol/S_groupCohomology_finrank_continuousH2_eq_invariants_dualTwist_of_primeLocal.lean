import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_groupCohomology_finrank_continuousH2_ofChar_cycloChar_of_primeLocal
import Theorems.Thm_Rep_isEquivariantBilinear_eval_dualTwist
import Theorems.Thm_Rep_dualTwist_smooth
import Theorems.Thm_groupCohomology_exists_theta0_and_theta2
import Theorems.Thm_groupCohomology_exists_theta1
import Theorems.Thm_groupCohomology_exists_level_ofChar_cycloChar_comp
import Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_primeLocal
import P2M.Util
namespace P2MW.S_groupCohomology_finrank_continuousH2_eq_invariants_dualTwist_of_primeLocal
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hq : (q : ℕ) = p)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)
    [FiniteDimensional (ZMod p) (continuousH2 (primeLocalToGlobal q) M)] :
    finrank (ZMod p) (continuousH2 (primeLocalToGlobal q) M)
      = finrank (ZMod p)
          (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))).ρ.invariants := by
  obtain ⟨hfinN, h1N⟩ := groupCohomology.finrank_continuousH2_ofChar_cycloChar_of_primeLocal (p := p) q
  haveI := hfinN
  let inv : continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) ≃ₗ[ZMod p] ZMod p :=
    LinearEquiv.ofFinrankEq _ _ (by rw [h1N, Module.finrank_self])
  have hφ := Rep.isEquivariantBilinear_eval_dualTwist M ((cycloChar p).comp (primeLocalToGlobal q))
  obtain ⟨⟨θ₀, hθ₀⟩, ⟨θ₂, hθ₂⟩⟩ := groupCohomology.exists_theta0_and_theta2 (primeLocalToGlobal q) _ hφ inv.toLinearMap
  obtain ⟨Fχ, hFχ, hχ1⟩ :=
    groupCohomology.exists_level_ofChar_cycloChar_comp (p := p) (primeLocalToGlobal q) (1 : ZMod p)
  have hsmD := Rep.dualTwist_smooth (primeLocalToGlobal q) M ((cycloChar p).comp (primeLocalToGlobal q)) hsm
    ⟨Fχ, hFχ, fun s hs => by
      have h : (((cycloChar p).comp (primeLocalToGlobal q) s : (ZMod p)ˣ) : ZMod p) * 1 = 1 := hχ1 s hs
      rw [mul_one] at h
      exact Units.val_eq_one.mp h⟩
  obtain ⟨θ₁, hθ₁⟩ := groupCohomology.exists_theta1 (primeLocalToGlobal q) _ hφ hsmD inv.toLinearMap
  obtain ⟨-, -, hb₂⟩ := groupCohomology.bijective_theta_dualTwist_of_primeLocal q M hsm inv.toLinearMap inv.bijective
    θ₀ hθ₀ θ₁ hθ₁ θ₂ hθ₂
  exact (LinearEquiv.ofBijective θ₂ hb₂).finrank_eq.trans Subspace.dual_finrank_eq
