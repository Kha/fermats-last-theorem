import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.RingTheory.PowerSeries.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one

set_option autoImplicit false

theorem LanglandsTunnell.RankinSelberg.mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one
    {R : Type*} [CommRing R] (a b e₁ e₂ e₃ : R)
    (t : ℕ → R) (ht0 : t 0 = 1) (ht1 : t 1 = a) (ht : ∀ m : ℕ, t (m + 2) = a * t (m + 1) - b * t m)
    (h : ℕ → R) (hh0 : h 0 = 1) (hh1 : h 1 = e₁) (hh2 : h 2 = e₁ ^ 2 - e₂)
    (hh : ∀ n : ℕ, h (n + 3) = e₁ * h (n + 2) - e₂ * h (n + 1) + e₃ * h n)
    (u : ℕ → ℕ → R) (hu0 : ∀ k : ℕ, u k 0 = h k)
    (hu : ∀ k₁ k₂ : ℕ, u k₁ (k₂ + 1) = h k₁ * h (k₂ + 1) - h (k₁ + 1) * h k₂) :
    PowerSeries.mk (fun n : ℕ => ∑ k₂ ∈ Finset.range (n / 2 + 1), b ^ k₂ * t (n - 2 * k₂) * u (n - k₂) k₂) *
        ↑(rsEulerPoly a b e₁ e₂ e₃) = (1 : PowerSeries R) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one.solution
