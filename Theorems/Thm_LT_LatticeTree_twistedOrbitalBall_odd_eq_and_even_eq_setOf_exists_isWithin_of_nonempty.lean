import Definitions.Def_LatticeTreeBaseChange
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_twistedOrbitalBall_odd_eq_and_even_eq_setOf_exists_isWithin_of_nonempty

set_option autoImplicit false

theorem LT.LatticeTree.twistedOrbitalBall_odd_eq_and_even_eq_setOf_exists_isWithin_of_nonempty
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (hne : (LT.LatticeTree.twistedFixedVertexSet δ σ).Nonempty) (m : ℕ) :
    LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
        (2 * m + 1) δ σ =
      LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
          (2 * m) δ σ ∧
    LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
        (2 * m) δ σ =
      {x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) m f x} := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_twistedOrbitalBall_odd_eq_and_even_eq_setOf_exists_isWithin_of_nonempty.solution
