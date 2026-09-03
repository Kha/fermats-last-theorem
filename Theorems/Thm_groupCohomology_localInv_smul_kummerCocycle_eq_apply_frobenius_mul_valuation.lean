import Mathlib
import Definitions.Def_GroupCohomology_LocalInvariant
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_localInv_smul_kummerCocycle_eq_apply_frobenius_mul_valuation
attribute [-instance] ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal
attribute [-simp] ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π IsLocalRing.principalUnits_zero

set_option autoImplicit false
open CategoryTheory ExtCitation groupCohomology

theorem groupCohomology.localInv_smul_kummerCocycle_eq_apply_frobenius_mul_valuation
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (q : Nat.Primes) [Fact ((q : ℕ)).Prime]
    (u : (PadicAlgCl q)ˣ) (hu : (u : PadicAlgCl q) = padicEmbedding q ζ)
    (χ : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → ℤ) (hχlc : IsLevelConstant₁ (localGaloisToGlobal q) χ)
    (hχ : ∀ σ τ : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q), (p : ℤ) ∣ χ σ + χ τ - χ (σ * τ))
    (hKχ : ∀ σ : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q),
      (∀ x : PadicAlgCl q, x ^ ((q : ℕ) ^ p - 1) = 1 → σ x = x) ↔ (p : ℤ) ∣ χ σ)
    (φ : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) (hφ : ∀ x : PadicAlgCl q, x ^ ((q : ℕ) ^ p - 1) = 1 → φ x = x ^ (q : ℕ))
    (a : ℚ_[q]ˣ) (α : (PadicAlgCl q)ˣ) (hα : algebraMap ℚ_[q] (PadicAlgCl q) (a : ℚ_[q]) = (α : PadicAlgCl q) ^ p)
    (z : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p)
    (hz : z ∈ levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
    (hcob : (fun g : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) => Additive.ofMul (u ^ (z g).val))
        - (fun g : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) =>
            (MonoidHom.toAdditive (rootsOfUnity p (PadicAlgCl q)).subtype).toIntLinearMap
              ((χ g.1) • (Kummer.kummerRep ℚ_[q] (PadicAlgCl q) p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2))))
        ∈ levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) :
    localInv p ζ q (continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) ⟨z, hz⟩)
      = ((χ φ : ℤ) : ZMod p) * (((Padic.valuation (a : ℚ_[q]) : ℤ)) : ZMod p) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_localInv_smul_kummerCocycle_eq_apply_frobenius_mul_valuation.solution
