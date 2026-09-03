import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_ringKrullDim_stalk_XO_le_two

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.ringKrullDim_stalk_XO_le_two
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (z : ↥(DRLevel.XO (N₀ := N₀) ρO)) :
    ringKrullDim ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk z) ≤ 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_ringKrullDim_stalk_XO_le_two.solution
