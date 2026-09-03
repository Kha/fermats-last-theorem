import Definitions.Def_LatticeTreeBaseChange
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_even_of_mem_fixedVertexSet_and_even_of_mem_orbitalBall_sdiff_of_det_eq_mul_zpow

set_option autoImplicit false

theorem LT.LatticeTree.even_of_mem_fixedVertexSet_and_even_of_mem_orbitalBall_sdiff_of_det_eq_mul_zpow
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (k : ℤ) (u : Rˣ)
    (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k) :
    (∀ x : LT.LatticeTree.Vertex R K, x ∈ LT.LatticeTree.fixedVertexSet (R := R) g → Even k) ∧
    ∀ (n : ℕ) (x : LT.LatticeTree.Vertex R K),
      x ∈
        LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) g \
          LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n) g →
      Even ((n : ℤ) + 1 - k) := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_even_of_mem_fixedVertexSet_and_even_of_mem_orbitalBall_sdiff_of_det_eq_mul_zpow.solution
