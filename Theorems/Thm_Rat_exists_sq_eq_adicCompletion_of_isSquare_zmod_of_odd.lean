import Mathlib
import P2M.Util
import P2M.Sol.S_Rat_exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem Rat.exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) (hsq : IsSquare (u : ZMod p)) :
    ∃ s : v.adicCompletion ℚ, s ^ 2 = algebraMap ℚ (v.adicCompletion ℚ) (u : ℚ) := by p2m_exact_reverting @_root_.P2MW.S_Rat_exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd.solution
