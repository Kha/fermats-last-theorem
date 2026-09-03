import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_existsUnique_isRoot_map_residue_eq_of_isRoot_of_derivative_ne_zero

set_option autoImplicit false

open IsLocalRing Polynomial

theorem HenselianLocalRing.existsUnique_isRoot_map_residue_eq_of_isRoot_of_derivative_ne_zero
    {A₀ : Type*} [CommRing A₀] (W : Type*) [CommRing W] [Algebra A₀ W] [IsLocalRing W] [HenselianLocalRing W]
    (h : A₀[X]) (hmonic : h.Monic) (tbar : ResidueField W)
    (hroot : ((h.map (algebraMap A₀ W)).map (IsLocalRing.residue W)).IsRoot tbar)
    (hsimple : ¬ ((h.map (algebraMap A₀ W)).derivative.map (IsLocalRing.residue W)).IsRoot tbar) :
    ∃! t : W, (h.map (algebraMap A₀ W)).IsRoot t ∧ IsLocalRing.residue W t = tbar := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_existsUnique_isRoot_map_residue_eq_of_isRoot_of_derivative_ne_zero.solution
