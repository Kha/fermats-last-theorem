import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character
import P2M.Util
import P2M.Sol.S_CuspidalType_character_unipotent_mul_diagElem

set_option autoImplicit false

open CuspidalType

theorem CuspidalType.character_unipotent_mul_diagElem
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (GL2 q) V)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) {a : (ZMod q)ˣ} (ha : a ≠ 1) (s : ZMod q) :
    ρ.character (unipotent q s * diagElem q a) = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_character_unipotent_mul_diagElem.solution
