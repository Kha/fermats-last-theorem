import Definitions.Def_LatticeTreeBaseChange
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet

set_option autoImplicit false

theorem LT.LatticeTree.finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (hfin : (LT.LatticeTree.twistedFixedVertexSet δ σ).Finite)
    (hne : (LT.LatticeTree.twistedFixedVertexSet δ σ).Nonempty) (r : ℕ) :
    ({x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (r + 1) f x} \
        {x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) r f x}).Finite ∧
    Nat.card ↥({x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (r + 1) f x} \
        {x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) r f x}) =
      (Nat.card ↥(LT.LatticeTree.twistedFixedVertexSet δ σ) * (Nat.card (R ⧸ Ideal.span {ϖ}) - 1) + 2) *
        Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet.solution
