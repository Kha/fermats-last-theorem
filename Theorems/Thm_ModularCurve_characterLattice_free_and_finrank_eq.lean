import Mathlib
import Definitions.Def_ModularCurve_ComponentGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_characterLattice_free_and_finrank_eq

set_option autoImplicit false

theorem ModularCurve.characterLattice_free_and_finrank_eq (S : Type*) [Fintype S] :
    Module.Free ℤ (ModularCurve.characterLattice S) ∧
      Module.finrank ℤ (ModularCurve.characterLattice S) = Fintype.card S - 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_characterLattice_free_and_finrank_eq.solution
