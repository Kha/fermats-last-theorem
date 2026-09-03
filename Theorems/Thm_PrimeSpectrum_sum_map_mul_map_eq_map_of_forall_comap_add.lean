import Mathlib
import P2M.Util
import P2M.Sol.S_PrimeSpectrum_sum_map_mul_map_eq_map_of_forall_comap_add

set_option autoImplicit false

open PrimeSpectrum

theorem PrimeSpectrum.sum_map_mul_map_eq_map_of_forall_comap_add
    {R S : Type*} [CommRing R] [CommRing S] {ι : Type*} [Fintype ι] [AddCommGroup ι]
    (φ₁₂ φ₂₃ φ₁₃ : R →+* S) (f : PrimeSpectrum R → ι) (e : ι → R)
    (he : CompleteOrthogonalIdempotents e)
    (hfe : ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e i ∉ x.asIdeal)
    (hf : ∀ y : PrimeSpectrum S, f (comap φ₁₂ y) + f (comap φ₂₃ y) = f (comap φ₁₃ y)) :
    ∀ k : ι, ∑ i, φ₁₂ (e i) * φ₂₃ (e (k - i)) = φ₁₃ (e k) := by p2m_exact_reverting @_root_.P2MW.S_PrimeSpectrum_sum_map_mul_map_eq_map_of_forall_comap_add.solution
