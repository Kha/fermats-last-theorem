import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_or

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.bcMap_genericPoint_specializes_or
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (y : ↥(DRLevel.XO (N₀ := N₀) ρO)) (hy : y ∉ (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    𝔛.ξinf ρO toκ ⤳ y ∨ 𝔛.ξzero ρO toκ ⤳ y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_or.solution
