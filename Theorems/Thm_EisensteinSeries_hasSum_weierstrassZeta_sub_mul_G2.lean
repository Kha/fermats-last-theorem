import Mathlib
import Definitions.Def_EisensteinSeries_WeierstrassZeta
import P2M.Util
import P2M.Sol.S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2

set_option autoImplicit false

open scoped Real

theorem EisensteinSeries.hasSum_weierstrassZeta_sub_mul_G2 (τ : UpperHalfPlane) (z : ℂ)
    (hz : ∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) :
    HasSum (fun m : ℕ => π * Complex.cot (π * (z + ((m : ℂ) + 1) * τ)) +
        π * Complex.cot (π * (z - ((m : ℂ) + 1) * τ)))
      (EisensteinSeries.weierstrassZeta τ z - z * EisensteinSeries.G2 τ -
        π * Complex.cot (π * z)) := by p2m_exact_reverting @_root_.P2MW.S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.solution
