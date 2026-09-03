import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_MazurPrincipleCore
import P2M.Util
import P2M.Sol.S_ModularCurve_SW_local_old_smul_top_eq_top_of_not_hasLowerLevelTorsion_aux2

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.SW_local_old_smul_top_eq_top_of_not_hasLowerLevelTorsion_aux2
    (p : ℕ) [Fact p.Prime] {N q q' : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq'p : q' ≠ p)
    [NeZero (N * q')] [NeZero N] [NeZero q] [Fact q.Prime] [Fact q'.Prime]
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hp : (p : HeckeAlg) ∈ 𝔪)
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')
    [DecidableEq (IsLocalRing.ResidueField ↥A₁)] [CharP (IsLocalRing.ResidueField ↥A₁) q']
    [Fintype ↥(ssPlaces q' (N * q) (IsLocalRing.ResidueField ↥A₁))]
    [Fintype ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))]
    [DecidableEq ↥(ssPlaces q' (N * q) (IsLocalRing.ResidueField ↥A₁))]
    [DecidableEq ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))]
    (X₁ : SSLevelDatum q' (IsLocalRing.ResidueField ↥A₁) N q) (hX₁ : X₁.HeckeLaws)
    {Xo₁ : Type} [AddCommGroup Xo₁] [Module HeckeAlg Xo₁] [Module.Finite ℤ Xo₁]
    (eX₁ : Xo₁ ≃+ (↥(characterLattice ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))) × ↥(characterLattice ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)))))
    (hT₁ : ∀ ℓ : Nat.Primes, ¬ ((ℓ : ℕ) ∣ N * q * q') → ∀ x : Xo₁,
        ((eX₁ (heckeGen ℓ • x)).1 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ) = (X₁.vertexHecke ℓ).mulVec ((eX₁ x).1 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ) ∧
        ((eX₁ (heckeGen ℓ • x)).2 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ) = (X₁.vertexHecke ℓ).mulVec ((eX₁ x).2 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ))
    (hU₁ : ∀ x : Xo₁,
        ((eX₁ (heckeGen ⟨q, hq⟩ • x)).1 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ) =
            (X₁.vertexHecke ⟨q, hq⟩).mulVec ((eX₁ x).1 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ) - ((eX₁ x).2 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ) ∧
        ((eX₁ (heckeGen ⟨q, hq⟩ • x)).2 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ) = ((q : ℕ) : ℤ) • ((eX₁ x).1 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ))
    (n₂ : Nat.Primes → ℤ) (hcol₂ : ∀ ℓ : Nat.Primes, HeckeRowSums (X₁.vertexHecke ℓ).transpose (n₂ ℓ))
    (ε₂ : letI := heckeModuleBar (N * q')
      ↥(toricMonodromyPart (J := JZero (N * q')) q' (A₁.inertiaSubgroupIn ℚ)) ≃+
        (↥(characterLattice ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))) →+ Additive (IsLocalRing.ResidueField ↥A₁)ˣ))
    (hε₂ : letI := heckeModuleBar (N * q')
      ∀ (ℓ : Nat.Primes), ¬ ((ℓ : ℕ) ∣ N * q * q') →
        ∀ (y : ↥(toricMonodromyPart (J := JZero (N * q')) q' (A₁.inertiaSubgroupIn ℚ)))
        (x : ↥(characterLattice ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)))),
        ε₂ (heckeGen ℓ • y) x = ε₂ y (heckeCharacterAction (X₁.vertexHecke ℓ).transpose (hcol₂ ℓ) x))
    (hreg : letI := heckeModuleBar (N * q')
      ¬ ∃ S : Finset Nat.Primes, (∀ ℓ ∈ S, (ℓ : ℕ) ∣ N * q * q') ∧
        HasLowerLevelTorsion S 𝔪 (JZero (N * q'))) :
    𝔪 • (⊤ : Submodule HeckeAlg Xo₁) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SW_local_old_smul_top_eq_top_of_not_hasLowerLevelTorsion_aux2.solution
