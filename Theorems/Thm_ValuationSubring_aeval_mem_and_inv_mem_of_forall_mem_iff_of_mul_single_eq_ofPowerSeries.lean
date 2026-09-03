import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_aeval_mem_and_inv_mem_of_forall_mem_iff_of_mul_single_eq_ofPowerSeries

set_option autoImplicit false

open Polynomial in

theorem ValuationSubring.aeval_mem_and_inv_mem_of_forall_mem_iff_of_mul_single_eq_ofPowerSeries
    {L : Type*} [Field L] (K : IntermediateField L (LaurentSeries L))
    {A : Type*} [CommRing A] [Algebra A ↥K] (φ : A →+* L) (hinj : Function.Injective φ)
    (hφ : ∀ a : A, ((algebraMap A ↥K a : ↥K) : LaurentSeries L) = HahnSeries.C (φ a))
    {κ : Type*} [CommRing κ] [Nontrivial κ] (res : A →+* κ)
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ g : ↥K, g ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map res ≠ 0 ∧
      (g : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map φ) = HahnSeries.ofPowerSeries ℤ L (x.map φ))
    (f : ↥K) (z : PowerSeries A) (m : ℕ) (hm : 0 < m)
    (hz : (f : LaurentSeries L) * HahnSeries.single (m : ℤ) 1 = HahnSeries.ofPowerSeries ℤ L (z.map φ))
    (hz1 : PowerSeries.coeff 0 z = 1)
    (Q : Polynomial A) (hQ : Q.map res ≠ 0) :
    Polynomial.aeval f Q ∈ W₀ ∧ (Polynomial.aeval f Q)⁻¹ ∈ W₀ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_aeval_mem_and_inv_mem_of_forall_mem_iff_of_mul_single_eq_ofPowerSeries.solution
