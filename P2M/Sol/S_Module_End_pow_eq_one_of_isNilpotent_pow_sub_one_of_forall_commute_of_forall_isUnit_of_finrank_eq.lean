import Mathlib
import Theorems.Thm_Module_End_eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq
import P2M.Util
namespace P2MW.S_Module_End_pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq

set_option autoImplicit false

theorem solution
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {D : Type*} [Ring D] [Algebra F D] (hD : ∀ x : D, x ≠ 0 → IsUnit x)
    (ι : D →ₐ[F] Module.End F V) (hdim : Module.finrank F D = Module.finrank F V)
    {g : Module.End F V} (hcomm : ∀ d : D, Commute (ι d) g) {e : ℕ}
    (he : IsNilpotent (g ^ e - 1)) : g ^ e = 1 :=
  sub_eq_zero.mp <|
    Module.End.eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq hD ι hdim
      (N := g ^ e - 1) (fun d => ((hcomm d).pow_right e).sub_right (Commute.one_right _)) he
