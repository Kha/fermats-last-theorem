import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Transfer
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hT : 𝒯.IsTree) (hfin : ∀ w : W, Finite (stabilizer G w))
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    (Γ' : Subgroup G) [Γ'.FiniteIndex] [GraphAction ↥Γ' 𝒯]
    [DecidableEq (QuotEdge G 𝒯)] [DecidableEq (QuotEdge ↥Γ' 𝒯)]
    {E₁ V₁ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁] (D₁ : DegeneracyData E₁ V₁)
    (eE₁ : E₁ ≃ {e : QuotEdge ↥Γ' 𝒯 // τ e.out.fst = 0})
    (hw₁ : ∀ e₁ : E₁, (D₁.w e₁ : ℕ) = Nat.card (stabilizer ↥Γ' (((eE₁ e₁).1).out : 𝒯.Dart)))
    {E₂ V₂ : Type} [Fintype E₂] [DecidableEq E₂] [DecidableEq V₂] (D₂ : DegeneracyData E₂ V₂)
    (eE₂ : E₂ ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (hw₂ : ∀ e₂ : E₂, (D₂.w e₂ : ℕ) = Nat.card (stabilizer G (((eE₂ e₂).1).out : 𝒯.Dart)))
    (μ : D₁.FiniteHom D₂)
    (hμE : ∀ e₁ : E₁, ((eE₂ (μ.mapE e₁)).1 : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) ((eE₁ e₁).1).out)
    (v₀ : W)
    (Φ₁ : Additive (Abelianization ↥Γ') →+ ↥(ribbonKernel D₁))
    (hΦ₁ : ∀ g : ↥Γ', (Φ₁ (Additive.ofMul (Abelianization.of g)) : E₁ → ℤ) = pathCycle 𝒯 (fun e => (eE₁ e).1) v₀ g)
    (Φ₂ : Additive (Abelianization G) →+ ↥(ribbonKernel D₂))
    (hΦ₂ : ∀ g : G, (Φ₂ (Additive.ofMul (Abelianization.of g)) : E₂ → ℤ) = pathCycle 𝒯 (fun e => (eE₂ e).1) v₀ g)
    (γ : G) :
    μ.pullback (Φ₂ (Additive.ofMul (Abelianization.of γ))) =
      Φ₁ (Additive.ofMul (MonoidHom.transfer (Abelianization.of : ↥Γ' →* Abelianization ↥Γ') γ)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer.solution
