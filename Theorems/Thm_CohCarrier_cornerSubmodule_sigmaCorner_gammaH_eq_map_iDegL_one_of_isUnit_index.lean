import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_LocalConditions
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_CohCarrier_cornerSubmodule_sigmaCorner_gammaH_eq_map_iDegL_one_of_isUnit_index

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open Polynomial IsLocalRing CohCarrier IharaLemma IharaTower

theorem CohCarrier.cornerSubmodule_sigmaCorner_gammaH_eq_map_iDegL_one_of_isUnit_index
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

    (L : ℕ) [NeZero L] (hL : L = M * r) (hrL : r ∣ L)
    (H : Subgroup (ZMod L)ˣ)
    (hH : ∀ v : (ZMod L)ˣ, v ∈ H ↔ ZMod.castHom hrL (ZMod r) (v : ZMod L) = 1)

    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 L H 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 L H 𝒪)]
    [Module.Finite 𝒪 𝕋]
    (Sp : IdempotentSplitting 𝕋) (i : Fin Sp.n)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i))]
    (tfull : CohCarrier.Gen L (↑S : Set ℕ) → 𝕋) (cfull : CohCarrier.Gen L (↑S : Set ℕ) → 𝒪)

    (hgen : ∀ x : 𝕋, ∃ f ∈ Algebra.adjoin 𝒪
        (CohCarrier.opFamily L H (↑S : Set ℕ) 𝒪 '' {g | (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M)}),
      ∀ m : H1 L H 𝒪, x • m = f m)
    (htfull : ∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ m : H1 L H 𝒪, tfull g • m = CohCarrier.opFamily L H (↑S : Set ℕ) 𝒪 g m)
    (hcfull : ∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      tfull g - algebraMap 𝒪 𝕋 (cfull g) ∈ Sp.𝔪 i)
    (hcofull : ∀ v : H1 L H 𝒪, (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ k : ℕ, ∃ n : ℕ, ((tfull g - algebraMap 𝒪 𝕋 (cfull g)) ^ n) • v ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 L H 𝒪))) →
      v ∈ cornerSubmodule (M := H1 L H 𝒪) (Sp.e i))

    (hcT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ L),
      IsLocalRing.residue 𝒪 (cfull (.T ℓ hℓ hℓS hℓL)) = θ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS))
    (hcU0 : ∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), q ∣ M → q ≠ p → q ^ 2 ∣ M →
      cfull (.U q hq hqL) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hcUp : ∀ (hpL : p ∣ L), p ∣ M → IsUnit (cfull (.U p Fact.out hpL)))
    (hcd : ∀ d : (ZMod L)ˣ, cfull (.dia d) - 1 ∈ IsLocalRing.maximalIdeal 𝒪)

    (hocc : cornerSubmodule (M := H1 L H 𝒪) (Sp.e i) ≠ ⊥)
    (hfaith : ∀ x : Sp.CornerRing i,
      (∀ m : ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i)), x • m = 0) → x = 0)

    {𝕋' : Type} [CommRing 𝕋'] [Algebra 𝒪 𝕋'] [Module 𝕋' (H1 L ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋' (H1 L ⊤ 𝒪)]
    [Module.Finite 𝒪 𝕋']
    (Sp' : IdempotentSplitting 𝕋') (i' : Fin Sp'.n)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i'))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i'))]
    (tfull' : CohCarrier.Gen L (↑S : Set ℕ) → 𝕋')

    (hgen' : ∀ x : 𝕋', ∃ f ∈ Algebra.adjoin 𝒪
        (CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 '' {g | (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M)}),
      ∀ m : H1 L ⊤ 𝒪, x • m = f m)
    (htfull' : ∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ m : H1 L ⊤ 𝒪, tfull' g • m = CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 g m)
    (hcfull' : ∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      tfull' g - algebraMap 𝒪 𝕋' (cfull g) ∈ Sp'.𝔪 i')
    (hcofull' : ∀ v : H1 L ⊤ 𝒪, (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
      ∀ k : ℕ, ∃ n : ℕ, ((tfull' g - algebraMap 𝒪 𝕋' (cfull g)) ^ n) • v ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 L ⊤ 𝒪))) →
      v ∈ cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i'))

    (hocc' : cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i') ≠ ⊥)
    (hfaith' : ∀ x : Sp'.CornerRing i',
      (∀ m : ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i')), x • m = 0) → x = 0)

    (h₁ : LevelLE L L ⊤ H 1) :

    (∀ v : H1 L H 𝒪, v ∈ cornerSubmodule (M := H1 L H 𝒪) (Sp.e i) ↔
      ∃ a : H1 L ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i') ∧ v = iDegL L L ⊤ H 1 𝒪 𝒪 h₁ a) ∧
    (∀ a : H1 L ⊤ 𝒪, a ∈ cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i') → iDegL L L ⊤ H 1 𝒪 𝒪 h₁ a = 0 → a = 0) ∧

    Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i)) =
      Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i')) ∧

    ∃ eD : Sp.CornerRing i ≃ₐ[𝒪] Sp'.CornerRing i',
      (∀ g : CohCarrier.Gen L (↑S : Set ℕ), (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L), g = CohCarrier.Gen.U q hq hqL → q ∣ M) →
        eD (Sp.toCornerRing i (tfull g)) = Sp'.toCornerRing i' (tfull' g)) ∧
      (∀ (x : Sp.CornerRing i) (a : ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i')))
          (v : ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i))),
        (v : H1 L H 𝒪) = iDegL L L ⊤ H 1 𝒪 𝒪 h₁ (a : H1 L ⊤ 𝒪) →
          ((x • v : ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i))) : H1 L H 𝒪) =
            iDegL L L ⊤ H 1 𝒪 𝒪 h₁ ((eD x • a : ↥(cornerSubmodule (M := H1 L ⊤ 𝒪) (Sp'.e i'))) : H1 L ⊤ 𝒪)) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_cornerSubmodule_sigmaCorner_gammaH_eq_map_iDegL_one_of_isUnit_index.solution
