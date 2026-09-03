import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import P2M.Util
import P2M.Sol.S_Representation_finrank_invariants_eq_one_of_natCard_map_eq_two

set_option autoImplicit false

open scoped MatrixGroups

universe u

theorem Representation.finrank_invariants_eq_one_of_natCard_map_eq_two
    {Γ : Type u} [Group Γ] {k : Type u} [Field k]
    (ρ : Γ →* GL (Fin 2) k) (I : Subgroup Γ)
    (hcard : Nat.card (I.map ρ) = 2)
    (hcent : ¬ I.map ρ ≤ Subgroup.center (GL (Fin 2) k)) :
    Module.finrank k
        (Representation.invariants
          ((Deformation.matrixRepresentation ρ).comp I.subtype)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_Representation_finrank_invariants_eq_one_of_natCard_map_eq_two.solution
