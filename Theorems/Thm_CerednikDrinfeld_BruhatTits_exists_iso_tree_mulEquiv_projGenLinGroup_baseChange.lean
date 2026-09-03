import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_BruhatTits_exists_iso_tree_mulEquiv_projGenLinGroup_baseChange

set_option autoImplicit false

open scoped MatrixGroups

theorem CerednikDrinfeld.BruhatTits.exists_iso_tree_mulEquiv_projGenLinGroup_baseChange
    (R' K' R K : Type) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Field K'] [Algebra R' K']
    [IsFractionRing R' K'] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K]
    (ι : LT.LatticeTree.IntegralHom R' K' R K) (ι' : LT.LatticeTree.IntegralHom R K R' K')
    (h₁ : ∀ x : K, ι.toField (ι'.toField x) = x) (h₂ : ∀ x : K', ι'.toField (ι.toField x) = x) :
    ∃ (e : CerednikDrinfeld.BruhatTits.tree R' K' ≃g CerednikDrinfeld.BruhatTits.tree R K)
      (ψ : PGL(2, K') ≃* PGL(2, K)),
      (∀ v : LT.LatticeTree.Vertex R' K', e v = LT.LatticeTree.Vertex.baseChange ι v) ∧
      (∀ g : GL (Fin 2) K', ψ (Matrix.ProjGenLinGroup.mk g) = Matrix.ProjGenLinGroup.mk (ι.mapGL g)) ∧
      (∀ (g : PGL(2, K')) (v : LT.LatticeTree.Vertex R' K'), e (g • v) = ψ g • e v) ∧
      e (LT.LatticeTree.stdVertex R' K') = LT.LatticeTree.stdVertex R K ∧
      ∀ (G : Type) [Group G] (ρ : G →* PGL(2, K')),
        {γ : G | (ψ.toMonoidHom.comp ρ) γ • LT.LatticeTree.stdVertex R K = LT.LatticeTree.stdVertex R K} =
          {γ : G | ρ γ • LT.LatticeTree.stdVertex R' K' = LT.LatticeTree.stdVertex R' K'} ∧
        (Function.Injective (ψ.toMonoidHom.comp ρ) ↔ Function.Injective ρ) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_BruhatTits_exists_iso_tree_mulEquiv_projGenLinGroup_baseChange.solution
