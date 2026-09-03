import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Mathlib.GroupTheory.Abelianization.Defs
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld CerednikDrinfeld.Mumford~vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter~pathCycle_eq_pathCycle_of_isTree~pathCycle_mulEquiv_eq_of_iso"

theorem CerednikDrinfeld.Mumford.apply_conj_eq_actZ_apply_of_apply_eq_pathCycle

    (K₀ : Type) [Field K₀]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [Mumford.GraphAction PGL(2, K₀) (BruhatTits.tree R₀ K₀)]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]

    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (eE : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E)

    [DecidableEq (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)
    (Φ : Additive (Abelianization ↥(Γ.map ρ)) →+ ↥(ribbonKernel D))
    (hΦ : ∀ γ : ↥(Γ.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φ (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel D)) : E → ℤ) (eE e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (n : G) (hn : n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G))
    (π : Equiv.Perm E) (s : ℤˣ)
    (hπ : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
        (ρ n ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → s = 1 ∧ (eE.symm (π (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out))) ∧
        (ρ n ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → s = -1 ∧ (eE.symm (π (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out).symm)))
    (A : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))
    (hA : ∀ (x : ↥(ribbonKernel D)) (e : E), (A x : E → ℤ) (π e) = ((s : ℤˣ) : ℤ) * (x : E → ℤ) e) :
    ∀ γ γ' : ↥(Γ.map ρ), (γ' : PGL(2, K₀)) = ρ n * (γ : PGL(2, K₀)) * (ρ n)⁻¹ →
      Φ (Additive.ofMul (Abelianization.of γ')) = A (Φ (Additive.ofMul (Abelianization.of γ))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle.solution
