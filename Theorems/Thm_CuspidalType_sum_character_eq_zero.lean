import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character
import P2M.Util
import P2M.Sol.S_CuspidalType_sum_character_eq_zero

set_option autoImplicit false

open CuspidalType

theorem CuspidalType.sum_character_eq_zero
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (GL2 q) V)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) :
    ∑ g : GL2 q, ρ.character g = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_sum_character_eq_zero.solution
