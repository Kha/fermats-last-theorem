import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_smul_mul_one_sub_eq_of_map_maximalIdeal_eq_top

set_option autoImplicit false

theorem IsLocalRing.exists_smul_mul_one_sub_eq_of_map_maximalIdeal_eq_top
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (H : Type) [CommRing H] [Algebra R H] (e : H) (he : IsIdempotentElem e)
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤) :
    ∀ d : R, d ≠ 0 → ∀ y : H, ∃ z : H, d • (z * (1 - e)) = y * (1 - e) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_smul_mul_one_sub_eq_of_map_maximalIdeal_eq_top.solution
