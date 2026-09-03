import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import P2M.Util
import P2M.Sol.S_ModularForm_alSlash_eq_alSlash_of_gammaH

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularForm.alSlash_eq_alSlash_of_gammaH
    (M : ℕ) [NeZero M] (q : ℕ) (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (W W' : ModularForm.AtkinLehnerDatum M q) (f : CuspForm (CohCarrier.GammaH M H) k) :
    ModularForm.alSlash W' k (⇑f) = ModularForm.alSlash W k (⇑f) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_alSlash_eq_alSlash_of_gammaH.solution
