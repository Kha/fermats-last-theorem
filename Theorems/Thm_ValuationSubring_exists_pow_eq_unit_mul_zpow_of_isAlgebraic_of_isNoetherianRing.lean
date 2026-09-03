import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_pow_eq_unit_mul_zpow_of_isAlgebraic_of_isNoetherianRing

set_option autoImplicit false

universe u

theorem ValuationSubring.exists_pow_eq_unit_mul_zpow_of_isAlgebraic_of_isNoetherianRing
    {L : Type u} [Field L] (A : ValuationSubring L)
    (A₀ : Type u) [CommRing A₀] [IsNoetherianRing A₀]
    (ι : A₀ →+* A) (hι : Function.Injective ι)
    (K₀ : Subfield L)
    (hrange : Set.range (fun a : A₀ => ((ι a : A) : L)) = (A : Set L) ∩ (K₀ : Set L))
    [Algebra.IsAlgebraic K₀ L]
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0) :
    ∀ x : L, x ≠ 0 → ∃ (N : ℕ) (a : ℤ) (u : Aˣ), 0 < N ∧ x ^ N = ((u : A) : L) * (π : L) ^ a := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_pow_eq_unit_mul_zpow_of_isAlgebraic_of_isNoetherianRing.solution
