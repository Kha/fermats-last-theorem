import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_QuasiFinite_exists_not_mem_finite_awayMap_of_mem_minimalPrimes

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem Algebra.QuasiFinite.exists_not_mem_finite_awayMap_of_mem_minimalPrimes
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [Algebra.QuasiFinite R A]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ r : R, r ∉ p ∧ (Localization.awayMap (algebraMap R A) r).Finite := by p2m_exact_reverting @_root_.P2MW.S_Algebra_QuasiFinite_exists_not_mem_finite_awayMap_of_mem_minimalPrimes.solution
