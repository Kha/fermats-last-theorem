import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_LT_LatticeTree_Vertex_isWithin_iff_dist_le
import Theorems.Thm_LT_LatticeTree_finite_setOf_isWithin_and_card_eq
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_BruhatTits_finite_setOf_dist_le

set_option autoImplicit false

open LT.LatticeTree

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (v : LT.LatticeTree.Vertex R K) (d : ℕ) :
    ({w : LT.LatticeTree.Vertex R K | (CerednikDrinfeld.BruhatTits.tree R K).dist v w ≤ d}).Finite := by
  have hset : {w : LT.LatticeTree.Vertex R K | (CerednikDrinfeld.BruhatTits.tree R K).dist v w ≤ d} =
      {w : LT.LatticeTree.Vertex R K |
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) d v w} := by
    ext w
    exact (LT.LatticeTree.Vertex.isWithin_iff_dist_le R K ϖ hϖ d v w).symm
  rw [hset]
  exact (LT.LatticeTree.finite_setOf_isWithin_and_card_eq R K ϖ hϖ v d).1
