import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_forall_localizedModule_mk_eq_of_forall_exists_chart

set_option autoImplicit false

universe u

theorem LinearMap.exists_forall_localizedModule_mk_eq_of_forall_exists_chart
    {B : Type u} [CommRing B] {T T' : Type u} [AddCommGroup T] [Module B T] [AddCommGroup T'] [Module B T']
    (φ : ∀ x : PrimeSpectrum B,
      LocalizedModule x.asIdeal.primeCompl T' →ₗ[B] LocalizedModule x.asIdeal.primeCompl T)
    (hφ : ∀ x : PrimeSpectrum B, ∃ (f : B) (_ : f ∉ x.asIdeal)
        (Φ : T' →ₗ[B] LocalizedModule (Submonoid.powers f) T),
        ∀ (y : PrimeSpectrum B), f ∉ y.asIdeal → ∀ (a : T') (t : T) (n : ℕ),
          Φ a = LocalizedModule.mk t ⟨f ^ n, Submonoid.mem_powers_iff _ _ |>.mpr ⟨n, rfl⟩⟩ →
            ∀ s : y.asIdeal.primeCompl, (s : B) = f ^ n →
              φ y (LocalizedModule.mk a 1) = LocalizedModule.mk t s) :
    ∃ τ : T' →ₗ[B] T, ∀ (x : PrimeSpectrum B) (a : T'),
      LocalizedModule.mk (τ a) 1 = φ x (LocalizedModule.mk a 1) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_forall_localizedModule_mk_eq_of_forall_exists_chart.solution
