import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct
import P2M.Util
namespace P2MW.S_LT_LatticeTree_nonempty_fixedVertexSet_or_exists_swap_of_iterate_act
set_option autoImplicit false

theorem solution
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
          LT.LatticeTree.Vertex.act g x₀ = x₁ ∧ LT.LatticeTree.Vertex.act g x₁ = x₀ := by
  have e : LT.LatticeTree.Vertex.twistedAct g (LT.LatticeTree.IntegralAut.refl R K) = LT.LatticeTree.Vertex.act g :=
    funext (LT.LatticeTree.Vertex.twistedAct_refl g)
  have h' := LT.LatticeTree.nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct R K ϖ hϖ
    (LT.LatticeTree.IntegralAut.refl R K) g m hm (by rw [e]; exact h)
  simp only [LT.LatticeTree.twistedFixedVertexSet_refl, e] at h'
  exact h'
