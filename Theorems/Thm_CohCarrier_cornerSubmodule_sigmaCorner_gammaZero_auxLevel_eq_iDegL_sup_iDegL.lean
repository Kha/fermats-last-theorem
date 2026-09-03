import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_LocalConditions
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_CohCarrier_cornerSubmodule_sigmaCorner_gammaZero_auxLevel_eq_iDegL_sup_iDegL
attribute [-instance] Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow
attribute [-simp] Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.gamma0UnitsHom_coe Ihara.gamma0UnitsChar_apply Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open Polynomial IsLocalRing CohCarrier IharaLemma IharaTower

theorem CohCarrier.cornerSubmodule_sigmaCorner_gammaZero_auxLevel_eq_iDegL_sup_iDegL
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)

    (M : ℕ) [NeZero M] (hMS : ∀ q : ℕ, q.Prime → q ∣ M → q ∈ S) (hMp : ¬ p ^ 2 ∣ M)
    (Smin : Finset ℕ) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))
    (hMmin : ∀ q ∈ Smin, q ≠ p → q ∣ M)
    (hMunr : ∀ q : ℕ, q.Prime → q ≠ p → q ∉ Smin → q ∣ M → q ^ 2 ∣ M)
    (hM3 : ∀ q : ℕ, q.Prime → q ≠ p → q ^ 2 ∣ M → ¬ q ^ 3 ∣ M)
    (htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)
    (hord : p ∣ M → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p)

    (r : ℕ) (hr : r.Prime) (hrS : r ∉ S) (hrM : ¬ r ∣ M) (hr1 : ¬ p ∣ r - 1)
    (hrρ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime r →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ r →
        LinearMap.trace (ResidueField 𝒪) ρbar.V (ρbar.ρ σ) ^ 2 ≠ ((r : ResidueField 𝒪) + 1) ^ 2)

    [Fact (CuspForm.HasIntegralStructure M 2)]
    (θ : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) * X + C (ℓ : ResidueField 𝒪))

    (L : ℕ) [NeZero L] (hL : L = M * r)

    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 L ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 L ⊤ 𝒪)]
    [Module.Finite 𝒪 𝕋]
    (Sp : IdempotentSplitting 𝕋) (i : Fin Sp.n)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i))]
    (tfull : CohCarrier.Gen L (↑S : Set ℕ) → 𝕋) (cfull : CohCarrier.Gen L (↑S : Set ℕ) → 𝒪)

    (hgen : ∀ x : 𝕋, ∃ f ∈ Algebra.adjoin 𝒪
        (CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 '' {g | (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M)}),
      ∀ m : H1 L ⊤ 𝒪, x • m = f m)
    (htfull : ∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ m : H1 L ⊤ 𝒪, tfull g • m = CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 g m)
    (hcfull : ∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      tfull g - algebraMap 𝒪 𝕋 (cfull g) ∈ Sp.𝔪 i)
    (hcofull : ∀ v : H1 L ⊤ 𝒪, (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ k : ℕ, ∃ n : ℕ, ((tfull g - algebraMap 𝒪 𝕋 (cfull g)) ^ n) • v ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 L ⊤ 𝒪))) →
      v ∈ cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i))

    (hcT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ L),
      IsLocalRing.residue 𝒪 (cfull (.T ℓ hℓ hℓS hℓL)) = θ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS))
    (hcU0 : ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), q ∣ M → q ≠ p → q ^ 2 ∣ M →
      cfull (.U q hq hqL) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hcUp : ∀ (hpL : p ∣ L), p ∣ M → IsUnit (cfull (.U p Fact.out hpL)))
    (hcd : ∀ d : (ZMod L)ˣ, cfull (.dia d) - 1 ∈ IsLocalRing.maximalIdeal 𝒪)

    (hocc : cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i) ≠ ⊥)
    (hfaith : ∀ x : Sp.CornerRing i,
      (∀ m : ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i)), x • m = 0) → x = 0)

    {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 M ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 M ⊤ 𝒪)]
    [Module.Finite 𝒪 𝕋₀]
    (Sp₀ : IdempotentSplitting 𝕋₀) (i₀ : Fin Sp₀.n)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))]
    (tfull₀ : CohCarrier.Gen M (↑(insert r S) : Set ℕ) → 𝕋₀) (cfull₀ : CohCarrier.Gen M (↑(insert r S) : Set ℕ) → 𝒪)
    (hgen₀ : ∀ x : 𝕋₀, ∃ f ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily M ⊤ (↑(insert r S) : Set ℕ) 𝒪)),
      ∀ m : H1 M ⊤ 𝒪, x • m = f m)
    (htfull₀ : ∀ g, ∀ m : H1 M ⊤ 𝒪, tfull₀ g • m = CohCarrier.opFamily M ⊤ (↑(insert r S) : Set ℕ) 𝒪 g m)
    (hcfull₀ : ∀ g, tfull₀ g - algebraMap 𝒪 𝕋₀ (cfull₀ g) ∈ Sp₀.𝔪 i₀)
    (hcofull₀ : ∀ v : H1 M ⊤ 𝒪, (∀ g, ∀ k : ℕ, ∃ n : ℕ, ((tfull₀ g - algebraMap 𝒪 𝕋₀ (cfull₀ g)) ^ n) • v ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 M ⊤ 𝒪))) →
      v ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))
    (hocc₀ : cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) ≠ ⊥)
    (hfaith₀ : ∀ x : Sp₀.CornerRing i₀,
      (∀ m : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)), x • m = 0) → x = 0)

    (hmatchT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ L)
        (hℓS' : ℓ ∉ (↑(insert r S) : Set ℕ)) (hℓM : ¬ ℓ ∣ M),
      cfull (.T ℓ hℓ hℓS hℓL) = cfull₀ (.T ℓ hℓ hℓS' hℓM))
    (hmatchU : ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L) (hqM : q ∣ M), cfull (.U q hq hqL) = cfull₀ (.U q hq hqM))
    (hcd₀ : ∀ d : (ZMod M)ˣ, cfull₀ (.dia d) - 1 ∈ IsLocalRing.maximalIdeal 𝒪)

    [NeZero r] (h1 : LevelLE M L ⊤ ⊤ 1) (hr' : LevelLE M L ⊤ ⊤ r)

    (hrig : Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i)) ≤
      2 * Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))) :

    (∀ v : H1 L ⊤ 𝒪, v ∈ cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i) ↔
      ∃ a b : H1 M ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) ∧
        b ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) ∧
        v = iDegL M L ⊤ ⊤ 1 𝒪 𝒪 h1 a + iDegL M L ⊤ ⊤ r 𝒪 𝒪 hr' b) ∧
    (∀ a b : H1 M ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) →
        b ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀) →
        iDegL M L ⊤ ⊤ 1 𝒪 𝒪 h1 a + iDegL M L ⊤ ⊤ r 𝒪 𝒪 hr' b = 0 → a = 0 ∧ b = 0) ∧

    Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i)) =
      2 * Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)) ∧

    ∃ eR : Sp.CornerRing i ≃ₐ[𝒪] Sp₀.CornerRing i₀,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ L)
          (hℓS' : ℓ ∉ (↑(insert r S) : Set ℕ)) (hℓM : ¬ ℓ ∣ M),
        eR (Sp.toCornerRing i (tfull (.T ℓ hℓ hℓS hℓL))) = Sp₀.toCornerRing i₀ (tfull₀ (.T ℓ hℓ hℓS' hℓM))) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L) (hqM : q ∣ M),
        eR (Sp.toCornerRing i (tfull (.U q hq hqL))) = Sp₀.toCornerRing i₀ (tfull₀ (.U q hq hqM))) ∧
      (∀ (x : Sp.CornerRing i) (a b : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀)))
          (v : ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i))),
        (v : H1 L ⊤ 𝒪) = iDegL M L ⊤ ⊤ 1 𝒪 𝒪 h1 (a : H1 M ⊤ 𝒪) + iDegL M L ⊤ ⊤ r 𝒪 𝒪 hr' (b : H1 M ⊤ 𝒪) →
          ((x • v : ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp.e i))) : H1 L ⊤ 𝒪) =
            iDegL M L ⊤ ⊤ 1 𝒪 𝒪 h1 ((eR x • a : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))) : H1 M ⊤ 𝒪) +
            iDegL M L ⊤ ⊤ r 𝒪 𝒪 hr' ((eR x • b : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp₀.e i₀))) : H1 M ⊤ 𝒪)) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_cornerSubmodule_sigmaCorner_gammaZero_auxLevel_eq_iDegL_sup_iDegL.solution
