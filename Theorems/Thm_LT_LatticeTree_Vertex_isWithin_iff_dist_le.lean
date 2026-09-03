import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_Vertex_isWithin_iff_dist_le

set_option autoImplicit false

open LT.LatticeTree

theorem LT.LatticeTree.Vertex.isWithin_iff_dist_le
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) (n : ℕ) (v w : LT.LatticeTree.Vertex R K) :
    LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v w ↔
      (CerednikDrinfeld.BruhatTits.tree R K).dist v w ≤ n := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_Vertex_isWithin_iff_dist_le.solution
