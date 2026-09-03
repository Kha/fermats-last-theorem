import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_etale_faithfullyFlat_finite_forall_exists_units_pow_eq_of_isUnit

set_option autoImplicit false

universe u

theorem Algebra.exists_etale_faithfullyFlat_finite_forall_exists_units_pow_eq_of_isUnit
    (R : Type u) [CommRing R] {m : ℕ} (n : Fin m → ℕ) (hn : ∀ i, 0 < n i) (hnu : ∀ i, IsUnit ((n i : ℕ) : R))
    (u : Fin m → Rˣ) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R') (_ : Module.FaithfullyFlat R R')
      (_ : Algebra.Etale R R') (v : Fin m → R'ˣ),
      ∀ i, (v i) ^ (n i) = Units.map (algebraMap R R' : R →* R') (u i) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_etale_faithfullyFlat_finite_forall_exists_units_pow_eq_of_isUnit.solution
