import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_residue_baseGerm_surjective_and_isClosed_crossingPt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.residue_baseGerm_surjective_and_isClosed_crossingPt
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)))
    (hinf : 𝔛.ξinf ρO toκ ⤳ 𝔛.crossingPt ρO toκ n) (hzero : 𝔛.ξzero ρO toκ ⤳ 𝔛.crossingPt ρO toκ n)
    (hrat : ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ DRLevel.XO (N₀ := N₀) ρO,
      s ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ∧
      s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = 𝔛.crossingPt ρO toκ n) :
    (Function.Surjective fun o : O =>
      IsLocalRing.residue ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n))
        (DRModelPackageLevel.baseGerm ρO (𝔛.crossingPt ρO toκ n) o)) ∧
    IsClosed ({𝔛.crossingPt ρO toκ n} : Set ↥(DRLevel.XO (N₀ := N₀) ρO)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_residue_baseGerm_surjective_and_isClosed_crossingPt.solution
