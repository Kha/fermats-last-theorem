import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_of_det_eq_mul_zpow
attribute [-simp] LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld LT.LatticeTree

theorem CerednikDrinfeld.BruhatTits.mem_typePreserving_iff_even_of_det_eq_mul_zpow
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    (K₀ : Type) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R₀ K₀)]
    (hact : ∀ (g : G) (x : LT.LatticeTree.Vertex R₀ K₀), g • x = ρ g • x)
    (g : G) (m : GL (Fin 2) K₀) (hm : ρ g = Matrix.ProjGenLinGroup.mk m)
    (u : R₀ˣ) (k : ℤ)
    (hdet : Matrix.det (m : Matrix (Fin 2) (Fin 2) K₀) = algebraMap R₀ K₀ u * algebraMap R₀ K₀ ϖ₀ ^ k) :
    g ∈ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) ↔ Even k := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_of_det_eq_mul_zpow.solution
