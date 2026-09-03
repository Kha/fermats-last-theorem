import Definitions.Def_LatticeTreeBaseChange
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_nonempty_fixedVertexSet_or_exists_swap_of_iterate_act

set_option autoImplicit false

theorem LT.LatticeTree.nonempty_fixedVertexSet_or_exists_swap_of_iterate_act
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (m : ℕ) (hm : 1 ≤ m)
    (h : (∃ x : LT.LatticeTree.Vertex R K, (LT.LatticeTree.Vertex.act g)^[m] x = x) ∨
      ∃ x₀ x₁ : LT.LatticeTree.Vertex R K,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          (LT.LatticeTree.Vertex.act g)^[m] x₀ = x₁ ∧ (LT.LatticeTree.Vertex.act g)^[m] x₁ = x₀) :
    (LT.LatticeTree.fixedVertexSet (R := R) g).Nonempty ∨
      ∃ x₀ x₁ : LT.LatticeTree.Vertex R K,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          LT.LatticeTree.Vertex.act g x₀ = x₁ ∧ LT.LatticeTree.Vertex.act g x₁ = x₀ := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_nonempty_fixedVertexSet_or_exists_swap_of_iterate_act.solution
