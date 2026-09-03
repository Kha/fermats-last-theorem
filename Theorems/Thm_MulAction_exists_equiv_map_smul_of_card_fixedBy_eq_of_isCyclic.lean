import Mathlib
import P2M.Util
import P2M.Sol.S_MulAction_exists_equiv_map_smul_of_card_fixedBy_eq_of_isCyclic

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem MulAction.exists_equiv_map_smul_of_card_fixedBy_eq_of_isCyclic
    {C : Type} [Group C] [IsCyclic C] [Finite C]
    {X Y : Type} [MulAction C X] [MulAction C Y] [Finite X] [Finite Y]
    (h : ∀ c : C, Nat.card (MulAction.fixedBy X c) = Nat.card (MulAction.fixedBy Y c)) :
    ∃ e : X ≃ Y, ∀ (c : C) (x : X), e (c • x) = c • e x := by p2m_exact_reverting @_root_.P2MW.S_MulAction_exists_equiv_map_smul_of_card_fixedBy_eq_of_isCyclic.solution
