import Mathlib
import P2M.Util
import P2M.Sol.S_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd

set_option autoImplicit false
open scoped nonZeroDivisors
theorem ClassGroup.exists_finset_forall_exists_mk0_eq_of_dvd
    (R : Type*) [CommRing R] [IsDedekindDomain R] [Finite (ClassGroup R)] :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum R), ∀ c : ClassGroup R, ∃ I : (Ideal R)⁰,
      ClassGroup.mk0 I = c ∧ ∀ v : IsDedekindDomain.HeightOneSpectrum R, v.asIdeal ∣ (I : Ideal R) → v ∈ S := by p2m_exact_reverting @_root_.P2MW.S_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd.solution
