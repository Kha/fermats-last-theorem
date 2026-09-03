import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import P2M.Util
import P2M.Sol.S_ExtCitation_comap_rootsOfUnity_levels_of_isOpen
attribute [-instance] ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open ExtCitation
theorem ExtCitation.comap_rootsOfUnity_levels_of_isOpen
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (N : ℕ) (hN : 0 < N) :
    (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).Normal ∧ (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).FiniteIndex ∧
    (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      F.fixingSubgroup.comap ((primeLocalToGlobal q).comp S.subtype) ≤ (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q)))) ∧
    (∃ φ : S, ∀ g : S, ∃ (n : ℤ) (u : S), u ∈ (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))) ∧ g = φ ^ n * u) ∧
    (∀ N' : ℕ, N ∣ N' → (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N' - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))) ≤ (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q)))) ∧
    (∃ N' : ℕ, 0 < N' ∧ N ∣ N' ∧ p ∣ ((Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N' - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q)))).relIndex (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q)))) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_comap_rootsOfUnity_levels_of_isOpen.solution
