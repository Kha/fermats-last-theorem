import Mathlib
import P2M.Util
import P2M.Sol.S_IsCyclotomicExtension_exists_int_dvd_pow_totient_and_algebraMap_eq_discr_powerBasis

set_option autoImplicit false

open Polynomial

universe u v

theorem IsCyclotomicExtension.exists_int_dvd_pow_totient_and_algebraMap_eq_discr_powerBasis
    {K : Type u} {L : Type v} [Field K] [CharZero K] [Field L] [Algebra K L] {n : ℕ} [NeZero n]
    [IsCyclotomicExtension {n} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ n) (hirr : Irreducible (cyclotomic n K)) :
    ∃ D : ℤ, D ∣ (n : ℤ) ^ n.totient ∧
      algebraMap ℤ K D = Algebra.discr K (fun i : Fin (hζ.powerBasis K).dim => (hζ.powerBasis K).gen ^ (i : ℕ)) := by p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_exists_int_dvd_pow_totient_and_algebraMap_eq_discr_powerBasis.solution
