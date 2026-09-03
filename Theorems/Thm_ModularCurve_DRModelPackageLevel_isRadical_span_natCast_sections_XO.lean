import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_isRadical_span_natCast_sections_XO

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.isRadical_span_natCast_sections_XO
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O) (hmax : (Ideal.span {((q : ℕ) : O)}).IsMaximal)
    (U : (DRLevel.XO (N₀ := N₀) ρO).affineOpens) :
    (Ideal.span {((q : ℕ) : Γ(DRLevel.XO (N₀ := N₀) ρO, U))}).IsRadical := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_isRadical_span_natCast_sections_XO.solution
