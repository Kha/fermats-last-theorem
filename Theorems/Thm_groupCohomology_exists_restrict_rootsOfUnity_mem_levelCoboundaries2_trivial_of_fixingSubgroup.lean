import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_restrict_rootsOfUnity_mem_levelCoboundaries2_trivial_of_fixingSubgroup
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open ExtCitation groupCohomology
open scoped IntermediateField
theorem groupCohomology.exists_restrict_rootsOfUnity_mem_levelCoboundaries2_trivial_of_fixingSubgroup
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ))) [FiniteDimensional ℚ_[(q : ℕ)] K]
    (hμ : ∀ ζ : PadicAlgCl (q : ℕ), ζ ^ p = 1 → ζ ∈ K)
    (a : ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) × ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q)))
      → Rep.trivial (ZMod p) ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) (ZMod p))
    (ha : a ∈ levelCocycles₂ ((primeLocalToGlobal q).comp (((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))).subtype)
      (Rep.trivial (ZMod p) ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) (ZMod p))) :
    ∃ (N : ℕ) (_ : 0 < N),
      (fun g : ↥((((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) ⊓ (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q)))
            × ↥((((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) ⊓ (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) =>
          a (Subgroup.inclusion inf_le_left g.1, Subgroup.inclusion inf_le_left g.2))
        ∈ levelCoboundaries₂
            (((primeLocalToGlobal q).comp (((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))).subtype).comp
              (Subgroup.inclusion (inf_le_left : (((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) ⊓ (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q)) ≤ (((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))))))
            (Rep.trivial (ZMod p) ↥((((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) ⊓ (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) (ZMod p)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_restrict_rootsOfUnity_mem_levelCoboundaries2_trivial_of_fixingSubgroup.solution
