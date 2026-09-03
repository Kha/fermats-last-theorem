import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_pathCycle_mulEquiv_eq_of_iso

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Mumford~pathCycle_eq_pathCycle_of_isTree MulAction"

theorem CerednikDrinfeld.Mumford.pathCycle_mulEquiv_eq_of_iso
    {G : Type} [Group G] {W : Type} [MulAction G W] [DecidableEq W]
    (𝒯 : SimpleGraph W) [CerednikDrinfeld.Mumford.GraphAction G 𝒯] (hT : 𝒯.IsTree)
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G 𝒯)] {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G 𝒯 // τ e.out.fst = 0})
    (φ : G ≃* G) (n : 𝒯 ≃g 𝒯) (hn : ∀ (g : G) (w : W), n (g • w) = φ g • n w)
    (π : E ≃ E) (s : ℤˣ)
    (hπ : ∀ (e : E) (d : 𝒯.Dart), Quotient.mk (MulAction.orbitRel G 𝒯.Dart) d = (eE e).1 →
      Quotient.mk (MulAction.orbitRel G 𝒯.Dart) (n.toHom.mapDart d) =
        (if s = 1 then (eE (π e)).1 else CerednikDrinfeld.Mumford.quotientReversal G 𝒯 (eE (π e)).1))
    (v₀ : W) (γ : G) (e : E) :
    CerednikDrinfeld.Mumford.pathCycle 𝒯 (fun e => (eE e).1) v₀ (φ γ) (π e) =
      (s : ℤ) * CerednikDrinfeld.Mumford.pathCycle 𝒯 (fun e => (eE e).1) v₀ γ e := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_pathCycle_mulEquiv_eq_of_iso.solution
