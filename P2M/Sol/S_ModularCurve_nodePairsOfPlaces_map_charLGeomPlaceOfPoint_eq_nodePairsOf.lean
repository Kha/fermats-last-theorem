import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SupersingularNodes
import P2M.Util
namespace P2MW.S_ModularCurve_nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf

set_option autoImplicit false

open AlgebraicCurve ModularCurve

private theorem bridgeHand_smulNodePair_eq_frobNodePair {K : Type*} [Field K] (q : ℕ)
    (g : SemilinearAut K (modularFunctionFieldC K 1))
    (hid : ∀ a : K, g • charLGeomPlaceOfPoint K a = charLGeomPlaceOfPoint K (a ^ q))
    (a : K) :
    smulNodePair g (charLGeomPlaceOfPoint K a) = frobNodePair q a :=
  Prod.ext rfl (hid a)

theorem solution
    {K : Type*} [Field K] (q : ℕ) (g : SemilinearAut K (modularFunctionFieldC K 1))
    (hid : ∀ a : K, g • charLGeomPlaceOfPoint K a = charLGeomPlaceOfPoint K (a ^ q))
    (S : Finset K) :
    nodePairsOfPlaces g
        (S.map ⟨charLGeomPlaceOfPoint K, charLGeomPlaceOfPoint_injective K⟩)
      = nodePairsOf q S := by
  unfold nodePairsOfPlaces nodePairsOf
  rw [Finset.map_map]
  congr 1
  refine DFunLike.ext _ _ (fun a => ?_)
  exact bridgeHand_smulNodePair_eq_frobNodePair q g hid a
