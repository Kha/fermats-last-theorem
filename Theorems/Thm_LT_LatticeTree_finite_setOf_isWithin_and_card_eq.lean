import Definitions.Def_LatticeTreeBaseChange
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_finite_setOf_isWithin_and_card_eq

set_option autoImplicit false

theorem LT.LatticeTree.finite_setOf_isWithin_and_card_eq
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (v : LT.LatticeTree.Vertex R K) (d : ℕ) :
    ({w : LT.LatticeTree.Vertex R K |
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) d v w}).Finite ∧
    Nat.card ↥({w : LT.LatticeTree.Vertex R K |
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) d v w}) =
      1 + ∑ r ∈ Finset.range d, (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_finite_setOf_isWithin_and_card_eq.solution
