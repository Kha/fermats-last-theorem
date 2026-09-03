import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_jDeg_comp_coeff

set_option autoImplicit false

theorem CohCarrier.jDeg_comp_coeff (M : ℕ) (H : Subgroup (ZMod M)ˣ) {A B : Type}
    [AddCommGroup A] [AddCommGroup B] {M' : ℕ} {H' : Subgroup (ZMod M')ˣ} {d : ℕ}
    [NeZero M'] [NeZero d] (h : LevelLE M M' H H' d) (g : A →+ B) (ψ : H1 M' H' A) :
    jDeg M M' H H' d B h (g.comp ψ) = g.comp (jDeg M M' H H' d A h ψ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_jDeg_comp_coeff.solution
