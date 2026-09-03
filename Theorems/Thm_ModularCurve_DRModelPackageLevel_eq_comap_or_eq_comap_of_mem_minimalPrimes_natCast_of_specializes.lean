import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    [hint : IsIntegral (DRLevel.XO (N₀ := N₀) ρO)]
    {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (x : ↥(DRLevel.XO (N₀ := N₀) ρO)) [IsNoetherianRing ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk x)]
    (hsp₁ : 𝔛.ξinf ρO toκ ⤳ x) (hsp₂ : 𝔛.ξzero ρO toκ ⤳ x) :
    (Ideal.comap ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _)).IsPrime ∧
    ((q : ℕ) : (DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk x) ∈ Ideal.comap ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _) ∧
    (Ideal.comap ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _)).IsPrime ∧
    ((q : ℕ) : (DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk x) ∈ Ideal.comap ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _) ∧
    (∀ 𝔭 : Ideal ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk x), 𝔭 ∈ (Ideal.span {((q : ℕ) : (DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk x)}).minimalPrimes →
      𝔭 = Ideal.comap ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _) ∨ 𝔭 = Ideal.comap ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _)) ∧
    (∀ (𝔭 : Ideal ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk x)) [𝔭.IsPrime], 𝔭.height = 1 → ((q : ℕ) : (DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk x) ∈ 𝔭 →
      𝔭 = Ideal.comap ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _) ∨ 𝔭 = Ideal.comap ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes.solution
