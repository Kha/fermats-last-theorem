import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_mk_eq_mk_expand_of_dvd_sub

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.exists_mk_eq_mk_expand_of_dvd_sub
    {W : Type*} [CommRing W] (π : W) [IsPrecomplete (Ideal.span {π}) W]
    (hsep : ∀ x : W, (∀ n : ℕ, π ^ n ∣ x) → x = 0) (e : ℕ) (he : e ≠ 0)
    (F : MvPowerSeries (Fin 2) W)
    (hF : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F ≠ 0 → (e : ℤ) ∣ (d 0 : ℤ) - d 1) :
    ∃ G : MvPowerSeries (Fin 2) W, mk π F = mk π (MvPowerSeries.expand e he G) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_mk_eq_mk_expand_of_dvd_sub.solution
