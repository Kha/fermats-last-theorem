import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_range_cuspInf_inter_range_iotaFin_eq_empty_and_range_cuspZero_inter_range_iotaFin_eq_empty
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
open scoped Polynomial

namespace ModularCurve.DRModelPackageLevel

theorem range_cuspInf_inter_range_iotaFin_eq_empty_and_range_cuspZero_inter_range_iotaFin_eq_empty
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) :
    Set.range 𝔓.εinf.1.base ∩ Set.range (IgusaScheme.ιFin (N₀ * q) q).base = ∅ ∧
    Set.range 𝔓.εzero.1.base ∩ Set.range (IgusaScheme.ιFin (N₀ * q) q).base = ∅ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_range_cuspInf_inter_range_iotaFin_eq_empty_and_range_cuspZero_inter_range_iotaFin_eq_empty.solution

end ModularCurve.DRModelPackageLevel
