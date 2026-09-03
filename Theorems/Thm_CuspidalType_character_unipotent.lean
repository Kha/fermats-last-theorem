import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character
import P2M.Util
import P2M.Sol.S_CuspidalType_character_unipotent

set_option autoImplicit false

open CuspidalType

theorem CuspidalType.character_unipotent
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hirr : ∀ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ → W.toSubmodule = ⊤)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) {t : ZMod q} (ht : t ≠ 0) :
    ρ.character (unipotent q t) = -1 := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_character_unipotent.solution
