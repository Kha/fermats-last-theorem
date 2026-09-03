import Definitions.Def_LatticeTreeBaseChange
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_exists_act_stdVertex_eq

set_option autoImplicit false

theorem LT.LatticeTree.exists_act_stdVertex_eq
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : LT.LatticeTree.Vertex R K) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) K,
      LT.LatticeTree.Vertex.act g (LT.LatticeTree.stdVertex R K) = v := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_exists_act_stdVertex_eq.solution
