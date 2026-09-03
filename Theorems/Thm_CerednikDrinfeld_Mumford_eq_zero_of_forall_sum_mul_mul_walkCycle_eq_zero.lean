import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_eq_zero_of_forall_sum_mul_mul_walkCycle_eq_zero
attribute [-simp] LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.eq_zero_of_forall_sum_mul_mul_walkCycle_eq_zero
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    {G : Type} [Group G] [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    [DecidableEq (QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E] (eE : E ≃ {e : QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})
    (w : E → ℤ) (hw : ∀ e : E, w e ≠ 0)
    (d : E → ℤ)
    (h : ∀ (g : GL (Fin 2) K₀)
      (p : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (LT.LatticeTree.stdVertex R K₀) (g • LT.LatticeTree.stdVertex R K₀)),
      ∑ e, w e * d e * walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) p e = 0) :
    d = 0 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_eq_zero_of_forall_sum_mul_mul_walkCycle_eq_zero.solution
