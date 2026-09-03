import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.OrderOfElement
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder
attribute [-simp] LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Omega.exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)] [GraphAction G (BruhatTits.tree R K₀)]
    (hρ : ActsThrough (LT.LatticeTree.Vertex R K₀) ρ) (hρinj : Function.Injective ρ)
    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    [Finite (QuotVert G (LT.LatticeTree.Vertex R K₀))]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    [DecidableEq (QuotEdge G (BruhatTits.tree R K₀))] [DecidableEq (QuotVert G (LT.LatticeTree.Vertex R K₀))]
    {E : Type} [Fintype E] (eE : E ≃ {e : QuotEdge G (BruhatTits.tree R K₀) // τ e.out.fst = 0})
    (f : ↥(holRing ϖ₁)) (hf : IsUnit f) (χ : G →* Kˣ)
    (haut : ∀ (γ : G) (z : ↥(upperHalfPlane K₀ K)),
      (f : ↥(upperHalfPlane K₀ K) → K) ((ρ γ) • z) = ((χ γ : Kˣ) : K) * (f : ↥(upperHalfPlane K₀ K) → K) z)
    (hχ : ∀ γ : G, IsOfFinOrder γ → χ γ = 1)

    (htame : ∀ w : LT.LatticeTree.Vertex R K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer G w) : ℕ) : K) = 1) :
    ∃ c : E → ℤ,
      c ∈ ribbonKernel
        (⟨fun e => Quotient.mk (orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.fst,
          fun e => Quotient.mk (orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.snd,
          fun _ => 1⟩ : DegeneracyData E (QuotVert G (LT.LatticeTree.Vertex R K₀))) ∧
      (∀ (g : GL (Fin 2) K₀)
        (p : (BruhatTits.tree R K₀).Walk (LT.LatticeTree.stdVertex R K₀) (g • LT.LatticeTree.stdVertex R K₀))
        (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K)
            ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
          Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
            Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
              (∑ e, ((stabWidth G (BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) * c e *
                walkCycle (BruhatTits.tree R K₀) (fun e => (eE e).1) p e)) ∧
      (c = 0 → ∀ z w : ↥(upperHalfPlane K₀ K),
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) = Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) w)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.solution
