import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_LT_LatticeTree_Vertex_isWithin_iff_dist_le
import Theorems.Thm_LT_LatticeTree_Vertex_isWithin_stdVertex_act_of_isInteger_of_det_eq
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_le_of_isInteger_of_det_eq

set_option autoImplicit false

open LT.LatticeTree

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hint : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j))
    (k : ℕ) (u : Rˣ)
    (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k) :
    (CerednikDrinfeld.BruhatTits.tree R K).dist (LT.LatticeTree.stdVertex R K)
      (g • LT.LatticeTree.stdVertex R K) ≤ k := by
  rw [← LT.LatticeTree.Vertex.isWithin_iff_dist_le R K ϖ hϖ]
  exact LT.LatticeTree.Vertex.isWithin_stdVertex_act_of_isInteger_of_det_eq R K ϖ hϖ g hint k u hdet
