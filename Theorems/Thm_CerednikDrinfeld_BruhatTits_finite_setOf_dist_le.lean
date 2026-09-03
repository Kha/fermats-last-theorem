import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_BruhatTits_finite_setOf_dist_le

set_option autoImplicit false

p2m_open "LT.LatticeTree~finite_setOf_isWithin_and_card_eq"

theorem CerednikDrinfeld.BruhatTits.finite_setOf_dist_le
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (v : LT.LatticeTree.Vertex R K) (d : ℕ) :
    ({w : LT.LatticeTree.Vertex R K | (CerednikDrinfeld.BruhatTits.tree R K).dist v w ≤ d}).Finite := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_BruhatTits_finite_setOf_dist_le.solution
