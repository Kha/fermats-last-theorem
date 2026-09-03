import Mathlib
import P2M.Util
import P2M.Sol.S_Rat_exists_sq_eq_adicCompletion_of_eight_dvd_sub_one

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem Rat.exists_sq_eq_adicCompletion_of_eight_dvd_sub_one
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (2 : 𝓞 ℚ) ∈ v.asIdeal) (u : ℤ) (hu : (8 : ℤ) ∣ u - 1) :
    ∃ s : v.adicCompletion ℚ, s ^ 2 = algebraMap ℚ (v.adicCompletion ℚ) (u : ℚ) := by p2m_exact_reverting @_root_.P2MW.S_Rat_exists_sq_eq_adicCompletion_of_eight_dvd_sub_one.solution
