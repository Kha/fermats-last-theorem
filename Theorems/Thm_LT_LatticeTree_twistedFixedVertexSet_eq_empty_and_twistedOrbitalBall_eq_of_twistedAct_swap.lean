import Definitions.Def_LatticeTreeBaseChange
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_twistedFixedVertexSet_eq_empty_and_twistedOrbitalBall_eq_of_twistedAct_swap

set_option autoImplicit false

theorem LT.LatticeTree.twistedFixedVertexSet_eq_empty_and_twistedOrbitalBall_eq_of_twistedAct_swap
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (x₀ x₁ : LT.LatticeTree.Vertex R K)
    (hadj : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁)
    (hne : x₀ ≠ x₁) (h₀ : LT.LatticeTree.Vertex.twistedAct δ σ x₀ = x₁)
    (h₁ : LT.LatticeTree.Vertex.twistedAct δ σ x₁ = x₀) (m : ℕ) :
    LT.LatticeTree.twistedFixedVertexSet δ σ = ∅ ∧
    LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
        (2 * m + 2) δ σ =
      LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
          (2 * m + 1) δ σ ∧
    LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)
        (2 * m + 1) δ σ =
      {x : LT.LatticeTree.Vertex R K |
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) m x₀ x ∨
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) m x₁ x} := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_twistedFixedVertexSet_eq_empty_and_twistedOrbitalBall_eq_of_twistedAct_swap.solution
