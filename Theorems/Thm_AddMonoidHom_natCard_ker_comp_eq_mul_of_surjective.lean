import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective

set_option autoImplicit false

theorem AddMonoidHom.natCard_ker_comp_eq_mul_of_surjective
    {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Nat.card (g.comp f).ker = Nat.card g.ker * Nat.card f.ker := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective.solution
