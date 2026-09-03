import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_forall_coeff_mem_iff_mem_pow_sup_map_of_forall_coeff_eq_zero_iff

set_option autoImplicit false

open PowerSeries

theorem RingHom.forall_coeff_mem_iff_mem_pow_sup_map_of_forall_coeff_eq_zero_iff
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (θ : A →+* PowerSeries R) (I : Ideal A)
    (hC : ∀ r : R, θ (algebraMap R A r) = PowerSeries.C r)
    (hfil : ∀ (n : ℕ) (a : A), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔ a ∈ I ^ n)
    (hsurj : ∀ (n : ℕ) (p : PowerSeries R), ∃ a : A, ∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = PowerSeries.coeff k p)
    (𝔪 : Ideal R) (n : ℕ) (a : A) :
    (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) ∈ 𝔪) ↔ a ∈ I ^ n ⊔ 𝔪.map (algebraMap R A) := by p2m_exact_reverting @_root_.P2MW.S_RingHom_forall_coeff_mem_iff_mem_pow_sup_map_of_forall_coeff_eq_zero_iff.solution
