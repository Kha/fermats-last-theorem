import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackage_locallyOfFinitePresentation_toBase

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModelPackage.locallyOfFinitePresentation_toBase (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) :
    LocallyOfFinitePresentation (DRModel.toBase p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackage_locallyOfFinitePresentation_toBase.solution
