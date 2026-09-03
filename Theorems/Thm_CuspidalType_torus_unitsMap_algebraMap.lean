import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_torus_unitsMap_algebraMap

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.torus_unitsMap_algebraMap (q : ℕ) [Fact q.Prime] (c : (ZMod q)ˣ) :
    torus q (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = scalarElem q c := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_torus_unitsMap_algebraMap.solution
