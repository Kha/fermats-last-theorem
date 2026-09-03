import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_not_isRoot_charpoly_torus

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.not_isRoot_charpoly_torus (q : ℕ) [Fact q.Prime] {α : (GaloisField q 2)ˣ}
    (hα : (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))) (x : ZMod q) :
    ¬ ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_not_isRoot_charpoly_torus.solution
