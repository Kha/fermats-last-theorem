import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero

set_option autoImplicit false

universe u v

theorem Polynomial.dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero
    {T : Type u} {S : Type v} [CommRing T] [CommRing S] (f : T →+* S) (hf : Function.Injective f)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (h : Polynomial T) (hh : h.Monic) (r : ι → S)
    (hsplit : h.map f = ∏ i, (Polynomial.X - Polynomial.C (r i)))
    (hsep : ∀ i j, i ≠ j → IsUnit (r i - r j))
    (F : Polynomial T) (hF : ∀ i, (F.map f).eval (r i) = 0) :
    h ∣ F := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero.solution
