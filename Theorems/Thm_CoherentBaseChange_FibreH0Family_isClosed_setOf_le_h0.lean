import Definitions.Def_AlgebraicGeometry_CoherentBaseChangeFamily
import P2M.Util
import P2M.Sol.S_CoherentBaseChange_FibreH0Family_isClosed_setOf_le_h0

universe u

open AlgebraicGeometry CoherentBaseChange

theorem CoherentBaseChange.FibreH0Family.isClosed_setOf_le_h0 {T : Scheme.{u}}
    (F : FibreH0Family T) (n : ℕ) :
    IsClosed {t : T | n ≤ F.h0 t} := by p2m_exact_reverting @_root_.P2MW.S_CoherentBaseChange_FibreH0Family_isClosed_setOf_le_h0.solution
