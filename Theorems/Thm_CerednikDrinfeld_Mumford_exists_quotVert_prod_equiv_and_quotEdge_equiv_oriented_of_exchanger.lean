import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_exists_quotVert_prod_equiv_and_quotEdge_equiv_oriented_of_exchanger

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.exists_quotVert_prod_equiv_and_quotEdge_equiv_oriented_of_exchanger
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hc : 𝒯.Connected) (hb : 𝒯.Colorable 2) (w₀ : W)
    (Δ : Subgroup G) (γ₀ : G) (hγ₀ : γ₀ ∈ Δ) (hγ₀' : γ₀ ∉ typePreserving G 𝒯 w₀) :
    ∃ (εV : QuotVert (↥Δ) W × Fin 2 ≃ QuotVert (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W)
      (εE : QuotEdge (↥Δ) 𝒯 ≃
        {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}),

      (∀ w : W, vertexType 𝒯 w₀ w = 0 →
        εV (Quotient.mk (MulAction.orbitRel (↥Δ) W) w, 0) =
          Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W) w) ∧
      (∀ w : W, vertexType 𝒯 w₀ w = 1 →
        εV (Quotient.mk (MulAction.orbitRel (↥Δ) W) w, 1) =
          Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) W) w) ∧

      (∀ d : 𝒯.Dart, vertexType 𝒯 w₀ d.fst = 0 →
        ((εE (Quotient.mk (MulAction.orbitRel (↥Δ) 𝒯.Dart) d) :
            {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}) :
            QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯) =
          Quotient.mk (MulAction.orbitRel (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯.Dart) d) ∧

      (∀ e : QuotEdge (↥Δ) 𝒯,
        (quotientDegeneracyData (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯).a ((εE e : {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}) : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯) =
          εV ((quotientDegeneracyData (↥Δ) 𝒯).a e, 0) ∧
        (quotientDegeneracyData (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯).b ((εE e : {e : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}) : QuotEdge (↥(Δ ⊓ typePreserving G 𝒯 w₀)) 𝒯) =
          εV ((quotientDegeneracyData (↥Δ) 𝒯).b e, 1)) ∧

      (∀ d : 𝒯.Dart,
        Nat.card (MulAction.stabilizer (↥Δ) d) = Nat.card (MulAction.stabilizer (↥(Δ ⊓ typePreserving G 𝒯 w₀)) d)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_exists_quotVert_prod_equiv_and_quotEdge_equiv_oriented_of_exchanger.solution
