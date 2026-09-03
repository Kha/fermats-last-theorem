import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SupersingularNodes
import P2M.Util
import P2M.Sol.S_ModularCurve_nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf

set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf
    {K : Type*} [Field K] (q : ℕ) (g : SemilinearAut K (modularFunctionFieldC K 1))
    (hid : ∀ a : K, g • charLGeomPlaceOfPoint K a = charLGeomPlaceOfPoint K (a ^ q))
    (S : Finset K) :
    nodePairsOfPlaces g
        (S.map ⟨charLGeomPlaceOfPoint K, charLGeomPlaceOfPoint_injective K⟩)
      = nodePairsOf q S := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf.solution
