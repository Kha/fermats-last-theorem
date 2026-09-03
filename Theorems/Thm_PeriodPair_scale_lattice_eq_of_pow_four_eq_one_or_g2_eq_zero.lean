import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import P2M.Util
import P2M.Sol.S_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero

set_option autoImplicit false

theorem PeriodPair.scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero (L : PeriodPair) (α : ℂˣ)
    (h₂ : (α : ℂ) ^ 4 = 1 ∨ L.g₂ = 0) (h₃ : (α : ℂ) ^ 6 = 1 ∨ L.g₃ = 0) :
    (L.scale α).lattice = L.lattice := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero.solution
