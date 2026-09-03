import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup
attribute [-simp] groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open ExtCitation groupCohomology
open scoped IntermediateField
theorem groupCohomology.exists_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (B : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) B]
    (hsm : ∀ b : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s b = b)
    (b : S × S → B) (hb : b ∈ levelCocycles₂ ((primeLocalToGlobal q).comp S.subtype) B) :
    ∃ (N : ℕ) (_ : 0 < N),
      (fun g : ↥(Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q)))
            × ↥(Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))) =>
          b ((Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).subtype g.1,
             (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).subtype g.2))
        ∈ levelCoboundaries₂
            (((primeLocalToGlobal q).comp S.subtype).comp (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).subtype)
            (Rep.res (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).subtype B) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal.solution
