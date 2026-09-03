import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_isReduced_pullback_toBase_of_isAlgClosed
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

namespace ModularCurve.DRModelPackageLevel

theorem isReduced_pullback_toBase_of_isAlgClosed
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (k : Type) [Field k] [IsAlgClosed k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DRLevel.R q))) :
    IsReduced (pullback (DRLevel.toBase N₀ q) x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_isReduced_pullback_toBase_of_isAlgClosed.solution

end ModularCurve.DRModelPackageLevel
