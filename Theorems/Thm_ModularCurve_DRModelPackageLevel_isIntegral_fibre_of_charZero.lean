import Definitions.Def_ModularCurve_DRModelPackageLevel
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_isIntegral_fibre_of_charZero
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

namespace ModularCurve.DRModelPackageLevel

theorem isIntegral_fibre_of_charZero
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (k : Type) [Field k] [CharZero k] (toκ : R q →+* k) :
    IsIntegral (fibre (N₀ := N₀) toκ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_isIntegral_fibre_of_charZero.solution

end ModularCurve.DRModelPackageLevel
