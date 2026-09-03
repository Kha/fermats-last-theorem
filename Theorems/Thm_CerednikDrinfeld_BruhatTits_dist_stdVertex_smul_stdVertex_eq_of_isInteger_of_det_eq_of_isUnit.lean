import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit
attribute [-simp] LocalGL2.swapUnit_val

set_option autoImplicit false

open LT.LatticeTree

theorem CerednikDrinfeld.BruhatTits.dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hint : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j))
    (k : ℕ) (u : Rˣ)
    (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k)
    (hunit : ∃ i j : Fin 2, ∃ w : Rˣ, (g : Matrix (Fin 2) (Fin 2) K) i j = algebraMap R K w) :
    (CerednikDrinfeld.BruhatTits.tree R K).dist (LT.LatticeTree.stdVertex R K)
      (g • LT.LatticeTree.stdVertex R K) = k := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit.solution
