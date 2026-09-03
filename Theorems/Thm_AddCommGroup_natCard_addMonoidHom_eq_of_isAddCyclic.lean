import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_AddCommGroup_natCard_addMonoidHom_eq_of_isAddCyclic

set_option autoImplicit false

open CategoryTheory
theorem AddCommGroup.natCard_addMonoidHom_eq_of_isAddCyclic {X Y : Type} [AddCommGroup X] [Finite X] [AddCommGroup Y] [Finite Y]
    [IsAddCyclic Y] (hX : ∀ x : X, Nat.card Y • x = 0) :
    Nat.card (X →+ Y) = Nat.card X := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_natCard_addMonoidHom_eq_of_isAddCyclic.solution
