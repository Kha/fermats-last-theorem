import Definitions.Def_LatticeTreeBaseChange
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_Vertex_isWithin_stdVertex_act_of_isInteger_of_det_eq

set_option autoImplicit false

open LT.LatticeTree

theorem LT.LatticeTree.Vertex.isWithin_stdVertex_act_of_isInteger_of_det_eq
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hint : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j))
    (k : ℕ) (u : Rˣ)
    (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k) :
    LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) k
      (LT.LatticeTree.stdVertex R K) (LT.LatticeTree.Vertex.act g (LT.LatticeTree.stdVertex R K)) := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_Vertex_isWithin_stdVertex_act_of_isInteger_of_det_eq.solution
