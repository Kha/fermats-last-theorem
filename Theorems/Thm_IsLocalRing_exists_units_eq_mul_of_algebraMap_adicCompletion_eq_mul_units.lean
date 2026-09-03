import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_units

set_option autoImplicit false

theorem IsLocalRing.exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_units
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B]
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal B) B)]
    (r s : B) (hs : s ≠ 0) (w : (AdicCompletion (IsLocalRing.maximalIdeal B) B)ˣ)
    (h : algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) r =
      algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) s * (w : AdicCompletion (IsLocalRing.maximalIdeal B) B)) :
    ∃ t : Bˣ, r = s * (t : B) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_units.solution
