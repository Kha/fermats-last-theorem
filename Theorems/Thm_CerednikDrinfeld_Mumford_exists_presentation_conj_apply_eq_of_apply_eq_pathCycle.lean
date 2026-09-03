import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Mathlib.GroupTheory.Abelianization.Defs
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_exists_presentation_conj_apply_eq_of_apply_eq_pathCycle

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.exists_presentation_conj_apply_eq_of_apply_eq_pathCycle
    {P : Type} [Group P] {W : Type} [MulAction P W] (𝒯 : SimpleGraph W) [GraphAction P 𝒯] (hT : 𝒯.IsTree)
    (τ : W → ZMod 2) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    (H : Subgroup P) [GraphAction ↥H 𝒯] (hH : ∀ (h : ↥H) (w : W), τ (h • w) = τ w)
    (p : P) (hp : ∀ w : W, τ (p • w) = τ w)
    (G₂ : Subgroup P) [GraphAction ↥G₂ 𝒯] (hHG₂ : ∀ h : P, h ∈ H → p⁻¹ * h * p ∈ G₂)
    (Γ' : Subgroup ↥G₂) [GraphAction ↥Γ' 𝒯] (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H)
    [DecidableEq (QuotEdge ↥H 𝒯)] [DecidableEq (QuotEdge ↥Γ' 𝒯)]
    {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (eE : E ≃ {e : QuotEdge ↥H 𝒯 // τ e.out.fst = 0})
    (eV : V ≃ QuotVert ↥H W)
    (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel ↥H W) (eE e).1.out.fst)
    (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel ↥H W) (eE e).1.out.snd)
    (v₀ : W)
    (Φ : Additive (Abelianization ↥H) →+ ↥(ribbonKernel D))
    (hΦ : ∀ h : ↥H, (Φ (Additive.ofMul (Abelianization.of h)) : E → ℤ) = pathCycle 𝒯 (fun e => (eE e).1) v₀ h) :
    ∃ (eE' : E ≃ {e : QuotEdge ↥Γ' 𝒯 // τ e.out.fst = 0}) (eV' : V ≃ QuotVert ↥Γ' W)
      (Φ' : Additive (Abelianization ↥Γ') →+ ↥(ribbonKernel D)),
      (∀ e : E, ((eE' e).1 : QuotEdge ↥Γ' 𝒯) = Quotient.mk (orbitRel ↥Γ' 𝒯.Dart) (p⁻¹ • (eE e).1.out)) ∧
      (∀ v : V, ∀ w : W, eV v = Quotient.mk (orbitRel ↥H W) w → eV' v = Quotient.mk (orbitRel ↥Γ' W) (p⁻¹ • w)) ∧
      (∀ e : E, eV' (D.a e) = Quotient.mk (orbitRel ↥Γ' W) (eE' e).1.out.fst) ∧
      (∀ e : E, eV' (D.b e) = Quotient.mk (orbitRel ↥Γ' W) (eE' e).1.out.snd) ∧
      (∀ γ : ↥Γ', (Φ' (Additive.ofMul (Abelianization.of γ)) : E → ℤ) = pathCycle 𝒯 (fun e => (eE' e).1) v₀ γ) ∧
      (∀ γ : ↥Γ', Φ' (Additive.ofMul (Abelianization.of γ)) =
        Φ (Additive.ofMul (Abelianization.of (⟨p * ((γ : ↥G₂) : P) * p⁻¹, (hΓ' (γ : ↥G₂)).1 γ.2⟩ : ↥H)))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_exists_presentation_conj_apply_eq_of_apply_eq_pathCycle.solution
