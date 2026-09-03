import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_isReduced_chartAlgFin_quotient_span_natCast
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
open scoped Polynomial

namespace ModularCurve.DRModelPackageLevel

theorem isReduced_chartAlgFin_quotient_span_natCast
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) :
    IsReduced (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))}) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_isReduced_chartAlgFin_quotient_span_natCast.solution

end ModularCurve.DRModelPackageLevel
