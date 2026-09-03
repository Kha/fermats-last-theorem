import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_perfectField_residueField_of_isAlgebraic_rat

set_option autoImplicit false

theorem IsLocalRing.perfectField_residueField_of_isAlgebraic_rat
    (L₀ : Type) [Field L₀] [CharZero L₀] [Algebra.IsAlgebraic ℚ L₀]
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsLocalRing A₀] [Algebra A₀ L₀]
    (hinj : Function.Injective (algebraMap A₀ L₀))
    (p : ℕ) [Fact p.Prime] (hp : (p : A₀) ∈ IsLocalRing.maximalIdeal A₀) :
    PerfectField (IsLocalRing.ResidueField A₀) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_perfectField_residueField_of_isAlgebraic_rat.solution
