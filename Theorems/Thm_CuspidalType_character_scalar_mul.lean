import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character
import P2M.Util
import P2M.Sol.S_CuspidalType_character_scalar_mul

set_option autoImplicit false

open CuspidalType

theorem CuspidalType.character_scalar_mul
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (GL2 q) V)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id) (c : (ZMod q)ˣ) (g : GL2 q) :
    ρ.character (scalarElem q c * g) = ρ.character g := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_character_scalar_mul.solution
