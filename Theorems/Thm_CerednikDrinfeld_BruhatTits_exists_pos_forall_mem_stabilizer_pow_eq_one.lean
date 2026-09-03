import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_BruhatTits_exists_pos_forall_mem_stabilizer_pow_eq_one
attribute [-simp] LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.BruhatTits.exists_pos_forall_mem_stabilizer_pow_eq_one
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Finite (IsLocalRing.ResidueField R₀)]
    (K₀ : Type) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    (Δ : Subgroup PGL(2, K₀))
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer ↥Δ d))
    [Finite (Mumford.QuotVert ↥Δ (LT.LatticeTree.Vertex R₀ K₀))] :
    ∃ m : ℕ, 0 < m ∧
      ∀ (w : LT.LatticeTree.Vertex R₀ K₀) (γ : ↥Δ), γ ∈ MulAction.stabilizer ↥Δ w → γ ^ m = 1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_BruhatTits_exists_pos_forall_mem_stabilizer_pow_eq_one.solution
