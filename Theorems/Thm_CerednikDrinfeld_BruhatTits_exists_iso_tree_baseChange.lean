import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_BruhatTits_exists_iso_tree_baseChange

set_option autoImplicit false

open scoped MatrixGroups

theorem CerednikDrinfeld.BruhatTits.exists_iso_tree_baseChange
    (R' K' R K : Type) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Field K'] [Algebra R' K']
    [IsFractionRing R' K'] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K]
    (ι : LT.LatticeTree.IntegralHom R' K' R K) (ι' : LT.LatticeTree.IntegralHom R K R' K')
    (h₁ : ∀ x : K, ι.toField (ι'.toField x) = x) (h₂ : ∀ x : K', ι'.toField (ι.toField x) = x) :
    ∃ e : CerednikDrinfeld.BruhatTits.tree R' K' ≃g CerednikDrinfeld.BruhatTits.tree R K,
      (∀ v : LT.LatticeTree.Vertex R' K', e v = LT.LatticeTree.Vertex.baseChange ι v) ∧
      (∀ v : LT.LatticeTree.Vertex R K, e.symm v = LT.LatticeTree.Vertex.baseChange ι' v) ∧
      (∀ (g : GL (Fin 2) K') (v : LT.LatticeTree.Vertex R' K'), e (g • v) = ι.mapGL g • e v) ∧
      e (LT.LatticeTree.stdVertex R' K') = LT.LatticeTree.stdVertex R K := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_BruhatTits_exists_iso_tree_baseChange.solution
