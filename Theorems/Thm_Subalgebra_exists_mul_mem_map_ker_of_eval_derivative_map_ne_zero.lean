import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_exists_mul_mem_map_ker_of_eval_derivative_map_ne_zero

open Polynomial

theorem Subalgebra.exists_mul_mem_map_ker_of_eval_derivative_map_ne_zero
    {P K L κ : Type*} [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    [Field K] [Algebra P K] [IsFractionRing P K]
    [Field L] [Algebra K L] [Algebra P L] [IsScalarTower P K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Field κ]
    (D : Subalgebra P L) (φ : ↥D →+* κ) (hφ : Function.Surjective (φ.comp (algebraMap P ↥D)))
    (t : ↥D) (ht : Algebra.adjoin K {(t : L)} = ⊤)
    (g : Polynomial P) (hg : g.Monic) (hgt : Polynomial.aeval t g = 0)
    (hsimple : ((g.map (φ.comp (algebraMap P ↥D))).derivative).eval (φ t) ≠ 0)
    (c : ↥D) (hcint : IsIntegral P (c : L)) (hc : φ c = 0) :
    ∃ s : ↥D, φ s ≠ 0 ∧
      s * c ∈ (RingHom.ker (φ.comp (algebraMap P ↥D))).map (algebraMap P ↥D) := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_exists_mul_mem_map_ker_of_eval_derivative_map_ne_zero.solution
