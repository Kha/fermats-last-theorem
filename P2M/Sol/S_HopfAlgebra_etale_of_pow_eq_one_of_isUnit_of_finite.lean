import Mathlib
import Theorems.Thm_HopfAlgebra_ker_counit_eq_sq_of_pow_eq_one_of_isUnit
import Theorems.Thm_HopfAlgebra_formallyUnramified_of_ker_counit_eq_sq
import P2M.Util
namespace P2MW.S_HopfAlgebra_etale_of_pow_eq_one_of_isUnit_of_finite

universe u v

set_option autoImplicit false

theorem solution
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    [IsNoetherianRing R] [Module.Finite R H] [Module.Flat R H]
    (n : ℕ) (hn : IsUnit (n : R))
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ n = 1) :
    Algebra.Etale R H := by
  haveI : Algebra.FinitePresentation R H := (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  haveI := HopfAlgebra.formallyUnramified_of_ker_counit_eq_sq
    (HopfAlgebra.ker_counit_eq_sq_of_pow_eq_one_of_isUnit (R := R) (H := H) n hn hH)
  exact Algebra.Etale.of_formallyUnramified_of_flat
