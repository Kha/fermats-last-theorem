import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.BruhatTits.adj_stdVertex_iff_eq_smul_of_uniformizer
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ)
    (n : GL (Fin 2) K₀) (hn : (n : Matrix (Fin 2) (Fin 2) K₀) = !![1, 0; 0, algebraMap R K₀ ϖ])
    (s : R → GL (Fin 2) K₀) (hs : ∀ t : R, (s t : Matrix (Fin 2) (Fin 2) K₀) = !![algebraMap R K₀ t, 1; 1, 0]) :
    (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) (n • LT.LatticeTree.stdVertex R K₀) ∧
    (∀ t : R, s t • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀) ∧
    (∀ y : LT.LatticeTree.Vertex R K₀, (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) y →
      y = n • LT.LatticeTree.stdVertex R K₀ ∨ ∃ t : R, y = (s t * n) • LT.LatticeTree.stdVertex R K₀) ∧
    (∀ t t' : R, (s t * n) • LT.LatticeTree.stdVertex R K₀ = (s t' * n) • LT.LatticeTree.stdVertex R K₀ ↔ ϖ ∣ t - t') ∧
    (∀ t : R, n • LT.LatticeTree.stdVertex R K₀ ≠ (s t * n) • LT.LatticeTree.stdVertex R K₀) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer.solution
