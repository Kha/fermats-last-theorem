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
import P2M.Util
import P2M.Sol.S_groupCohomology_bijective_theta_dualTwist_of_res
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.bijective_theta_dualTwist_of_res
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q)) [S.FiniteIndex] (hSp : IsUnit ((S.index : ℕ) : ZMod p))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)
    (inv : continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p] ZMod p)
    (hinv : Function.Bijective inv)
    (hres : ∀ (invS : continuousH2 ((primeLocalToGlobal q).comp S.subtype)
        (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) →ₗ[ZMod p] ZMod p),
      Function.Bijective invS →
      ∀ (θ₀ : (Rep.res S.subtype M).ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))),
        IsTheta0 ((primeLocalToGlobal q).comp S.subtype)
          (Module.Dual.eval (ZMod p) M : Rep.res S.subtype M →ₗ[ZMod p]
            Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p]
            Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) invS θ₀ →
      ∀ (θ₁ : continuousH1 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH1 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))),
        IsTheta1 ((primeLocalToGlobal q).comp S.subtype)
          (Module.Dual.eval (ZMod p) M : Rep.res S.subtype M →ₗ[ZMod p]
            Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p]
            Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) invS θ₁ →
      ∀ (θ₂ : continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))).ρ.invariants),
        IsTheta2 ((primeLocalToGlobal q).comp S.subtype)
          (Module.Dual.eval (ZMod p) M : Rep.res S.subtype M →ₗ[ZMod p]
            Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p]
            Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) invS θ₂ →
      Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂)
    (θ₀ : M.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
      (continuousH2 (primeLocalToGlobal q) (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))
    (hθ₀ : IsTheta0 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)) →ₗ[ZMod p]
        ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) inv θ₀)
    (θ₁ : continuousH1 (primeLocalToGlobal q) M →ₗ[ZMod p] Module.Dual (ZMod p)
      (continuousH1 (primeLocalToGlobal q) (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))
    (hθ₁ : IsTheta1 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)) →ₗ[ZMod p]
        ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) inv θ₁)
    (θ₂ : continuousH2 (primeLocalToGlobal q) M →ₗ[ZMod p] Module.Dual (ZMod p)
      (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))).ρ.invariants)
    (hθ₂ : IsTheta2 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)) →ₗ[ZMod p]
        ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) inv θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_bijective_theta_dualTwist_of_res.solution
