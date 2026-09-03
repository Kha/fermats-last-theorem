import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two

set_option autoImplicit false

open CerednikDrinfeld.BruhatTits LT.LatticeTree

theorem CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] :
    (tree R K).Connected ∧ (tree R K).Colorable 2 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two.solution
