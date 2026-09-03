import Definitions.Def_LatticeTreeBaseChange
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_finite_setOf_isWithin_or_isWithin_and_card_eq_of_isWithin_one

set_option autoImplicit false

theorem LT.LatticeTree.finite_setOf_isWithin_or_isWithin_and_card_eq_of_isWithin_one
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (x₀ x₁ : LT.LatticeTree.Vertex R K)
    (hadj : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁)
    (hne : x₀ ≠ x₁) (r : ℕ) :
    ({x : LT.LatticeTree.Vertex R K |
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) r x₀ x ∨
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) r x₁ x}).Finite ∧
    Nat.card ↥({x : LT.LatticeTree.Vertex R K |
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) r x₀ x ∨
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) r x₁ x}) =
      2 * ∑ i ∈ Finset.range (r + 1), Nat.card (R ⧸ Ideal.span {ϖ}) ^ i := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_finite_setOf_isWithin_or_isWithin_and_card_eq_of_isWithin_one.solution
