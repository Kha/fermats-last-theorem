import Mathlib
import P2M.Util
import P2M.Sol.S_PrimeSpectrum_forall_sub_apply_eq_iff

set_option autoImplicit false

open PrimeSpectrum

theorem PrimeSpectrum.forall_sub_apply_eq_iff {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [AddCommGroup ι]
    (f g : PrimeSpectrum R → ι) (e e' : ι → R)
    (hfe : ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e i ∉ x.asIdeal)
    (hge : ∀ (i : ι) (x : PrimeSpectrum R), g x = i ↔ e' i ∉ x.asIdeal) :
    ∀ (k : ι) (x : PrimeSpectrum R), f x - g x = k ↔ (∑ i, e i * e' (i - k)) ∉ x.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_PrimeSpectrum_forall_sub_apply_eq_iff.solution
