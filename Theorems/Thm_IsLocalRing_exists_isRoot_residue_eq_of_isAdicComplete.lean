import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_isRoot_residue_eq_of_isAdicComplete

set_option autoImplicit false

open Polynomial IsLocalRing in

theorem IsLocalRing.exists_isRoot_residue_eq_of_isAdicComplete
    {C : Type*} [CommRing C] [IsLocalRing C] [IsAdicComplete (maximalIdeal C) C]
    (p : C[X]) (hp : p.Monic) (α : ResidueField C)
    (hα : (p.map (residue C)).IsRoot α) (hα' : ¬ (derivative (p.map (residue C))).IsRoot α) :
    ∃ x : C, p.IsRoot x ∧ residue C x = α := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_isRoot_residue_eq_of_isAdicComplete.solution
