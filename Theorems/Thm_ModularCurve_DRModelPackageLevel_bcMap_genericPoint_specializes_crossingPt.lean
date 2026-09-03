import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_crossingPt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.bcMap_genericPoint_specializes_crossingPt
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1))) :
    𝔛.ξinf ρO toκ ⤳ 𝔛.crossingPt ρO toκ n ∧ 𝔛.ξzero ρO toκ ⤳ 𝔛.crossingPt ρO toκ n := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_crossingPt.solution
