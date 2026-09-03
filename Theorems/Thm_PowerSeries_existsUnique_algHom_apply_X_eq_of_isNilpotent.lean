import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_existsUnique_algHom_apply_X_eq_of_isNilpotent

set_option autoImplicit false

theorem PowerSeries.existsUnique_algHom_apply_X_eq_of_isNilpotent
    {A : Type} [CommRing A] {T : Type} [CommRing T] [Algebra A T] (t : T) (ht : IsNilpotent t) :
    (∃! φ : PowerSeries A →ₐ[A] T, φ PowerSeries.X = t) ∧
    (∀ φ : PowerSeries A →ₐ[A] T, φ PowerSeries.X = t → ∀ N : ℕ, t ^ N = 0 →
      ∀ f : PowerSeries A, φ f = ∑ i ∈ Finset.range N, algebraMap A T (PowerSeries.coeff i f) * t ^ i) := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_existsUnique_algHom_apply_X_eq_of_isNilpotent.solution
