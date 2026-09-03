import Mathlib
import P2M.Util
namespace P2MW.S_Polynomial_dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero

set_option autoImplicit false

universe u v

open Polynomial in
theorem solution
    {T : Type u} {S : Type v} [CommRing T] [CommRing S] (f : T →+* S) (hf : Function.Injective f)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (h : Polynomial T) (hh : h.Monic) (r : ι → S)
    (hsplit : h.map f = ∏ i, (Polynomial.X - Polynomial.C (r i)))
    (hsep : ∀ i j, i ≠ j → IsUnit (r i - r j))
    (F : Polynomial T) (hF : ∀ i, (F.map f).eval (r i) = 0) :
    h ∣ F := by
  classical

  have hdvdS : h.map f ∣ F.map f := by
    rw [hsplit]
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (hsep i j hij)
    · intro i _
      exact Polynomial.dvd_iff_isRoot.mpr (hF i)

  have hR : F %ₘ h = 0 := by
    apply Polynomial.map_injective f hf
    rw [Polynomial.map_modByMonic f hh, Polynomial.map_zero]
    exact (Polynomial.modByMonic_eq_zero_iff_dvd (hh.map f)).mpr hdvdS
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hh).mp hR
