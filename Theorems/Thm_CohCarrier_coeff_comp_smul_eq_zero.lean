import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_coeff_comp_smul_eq_zero

set_option autoImplicit false

theorem CohCarrier.coeff_comp_smul_eq_zero (M : ℕ) (H : Subgroup (ZMod M)ˣ) {A B : Type}
    [AddCommGroup A] [AddCommGroup B] {R : Type*} [Semiring R] [Module R A] (g : A →+ B) (ϖ : R)
    (hg : ∀ a : A, g (ϖ • a) = 0) (φ : H1 M H A) :
    g.comp (ϖ • φ) = 0 := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_coeff_comp_smul_eq_zero.solution
