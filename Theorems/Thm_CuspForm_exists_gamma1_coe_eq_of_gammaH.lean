import Definitions.Def_CohCarrier_Level
import Mathlib.NumberTheory.ModularForms.Basic
import P2M.Util
import P2M.Sol.S_CuspForm_exists_gamma1_coe_eq_of_gammaH

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_gamma1_coe_eq_of_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (f : CuspForm (CohCarrier.GammaH M H) k) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 M) k, (⇑g : UpperHalfPlane → ℂ) = ⇑f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_gamma1_coe_eq_of_gammaH.solution
