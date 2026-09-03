import Mathlib
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_CharacterLatticePairings
import P2M.Util
import P2M.Sol.S_ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const

set_option autoImplicit false

theorem ModularCurve.characterLattice_evalHom_surjective_and_trivial_iff_const
    (S : Type*) [Fintype S] [Nonempty S] (G : Type*) [CommGroup G] :
    (∀ χ : ModularCurve.characterLattice S →+ Additive G,
        ∃ w : S → G, ∀ a, Additive.toMul (χ a) = ModularCurve.CharacterLattice.evalHom a w) ∧
    (∀ w : S → G, (∀ a : ModularCurve.characterLattice S, ModularCurve.CharacterLattice.evalHom a w = 1) ↔
        ∃ c : G, w = fun _ => c) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const.solution
