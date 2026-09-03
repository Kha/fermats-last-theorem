import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_comp_surjective_of_forall_exists_eq_crossingCoord

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.comp_surjective_of_forall_exists_eq_crossingCoord
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) {G : Type*} [AddCommGroup G] (comp : G →+ componentGroup e)
    (h : ∀ s : ι, ∃ x : G, comp x = componentGroupProj e (crossingCoord s)) :
    Function.Surjective comp := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_comp_surjective_of_forall_exists_eq_crossingCoord.solution
