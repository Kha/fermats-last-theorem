import Mathlib
import P2M.Util
import P2M.Sol.S_Module_sum_dual_apply_eq_natCast_of_rankAtStalk_eq

set_option autoImplicit false

universe u v

open scoped BigOperators

theorem Module.sum_dual_apply_eq_natCast_of_rankAtStalk_eq
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {n : ℕ} (x : Fin n → M) (φ : Fin n → (M →ₗ[A] A)) (hxφ : ∀ m : M, ∑ i, φ i m • x i = m)
    (d : ℕ) (hd : ∀ p : PrimeSpectrum A, Module.rankAtStalk M p = d) :
    ∑ i, φ i (x i) = (d : A) := by p2m_exact_reverting @_root_.P2MW.S_Module_sum_dual_apply_eq_natCast_of_rankAtStalk_eq.solution
