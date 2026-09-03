import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_nonempty_twoAffineOpenCover_fibre0

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.nonempty_twoAffineOpenCover_fibre0
    {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
    {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ) :
    Nonempty (DRLevel.fibre0 (N₀ := N₀) toκ).TwoAffineOpenCover := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_twoAffineOpenCover_fibre0.solution
