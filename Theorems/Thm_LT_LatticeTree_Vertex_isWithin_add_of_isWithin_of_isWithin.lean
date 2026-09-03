import Definitions.Def_LatticeTreeBaseChange
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_Vertex_isWithin_add_of_isWithin_of_isWithin

set_option autoImplicit false

theorem LT.LatticeTree.Vertex.isWithin_add_of_isWithin_of_isWithin
    (R K : Type) [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (v w x : LT.LatticeTree.Vertex R K) (n m : ℕ)
    (h₁ : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v w)
    (h₂ : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) m w x) :
    LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + m) v x := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_Vertex_isWithin_add_of_isWithin_of_isWithin.solution
