import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_torus_injective

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.torus_injective (q : ℕ) [Fact q.Prime] : Function.Injective (torus q) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_torus_injective.solution
