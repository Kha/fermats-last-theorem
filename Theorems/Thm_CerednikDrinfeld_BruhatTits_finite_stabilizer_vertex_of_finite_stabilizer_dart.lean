import Mathlib
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_BruhatTits_finite_stabilizer_vertex_of_finite_stabilizer_dart
attribute [-simp] LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction LT.LatticeTree

theorem CerednikDrinfeld.BruhatTits.finite_stabilizer_vertex_of_finite_stabilizer_dart
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    (K₀ : Type) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (G : Type) [Group G] [MulAction G (LT.LatticeTree.Vertex R₀ K₀)] [GraphAction G (BruhatTits.tree R₀ K₀)]
    (hfinD : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (stabilizer G d))
    (v : LT.LatticeTree.Vertex R₀ K₀) : Finite (stabilizer G v) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_BruhatTits_finite_stabilizer_vertex_of_finite_stabilizer_dart.solution
