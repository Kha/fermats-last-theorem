import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_gaussPresentation_qExpand_iff

set_option autoImplicit false

theorem ModularCurve.exists_gaussPresentation_qExpand_iff
    (A : Type) [CommRing A] [IsLocalRing A] (L : Type) [Field L] [Algebra A L]
    (N : ℕ) [NeZero N] (g : LaurentSeries L) :
    (∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      ModularCurve.qExpand L N g * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) ↔
    (∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      g * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_gaussPresentation_qExpand_iff.solution
