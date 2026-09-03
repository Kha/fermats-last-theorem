import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_not_isOpen_singleton_fibre

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.not_isOpen_singleton_fibre
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
    (w : DRLevel.fibre (N₀ := N₀) toκ) : ¬ IsOpen ({w} : Set (DRLevel.fibre (N₀ := N₀) toκ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_not_isOpen_singleton_fibre.solution
