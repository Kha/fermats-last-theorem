import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_forall_v_eq_one_apply_eq_prod_zpow_pathCycle

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld.Mumford~exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle~surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle"

theorem CerednikDrinfeld.Omega.exists_forall_v_eq_one_apply_eq_prod_zpow_pathCycle
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀]
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    {G : Type} [Group G]
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]

    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)

    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})

    (η : G →* Kˣ) (hη₁ : ∀ β : G, Valued.v ((η β : Kˣ) : K) = 1) (hη : ∀ γ : G, IsOfFinOrder γ → η γ = 1) :
    ∃ ζ : E → Kˣ, (∀ e : E, Valued.v ((ζ e : Kˣ) : K) = 1) ∧
      ∀ β : G, ((η β : Kˣ) : K) = ∏ e : E, ((ζ e : Kˣ) : K) ^
        CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
          (LT.LatticeTree.stdVertex R K₀) β e := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_forall_v_eq_one_apply_eq_prod_zpow_pathCycle.solution
