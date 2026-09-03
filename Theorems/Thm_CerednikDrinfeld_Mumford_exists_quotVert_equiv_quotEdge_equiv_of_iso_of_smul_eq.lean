import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_exists_quotVert_equiv_quotEdge_equiv_of_iso_of_smul_eq

set_option autoImplicit false

open CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.exists_quotVert_equiv_quotEdge_equiv_of_iso_of_smul_eq
    {G₁ G₂ : Type} [Group G₁] [Group G₂] {W₁ W₂ : Type} [MulAction G₁ W₁] [MulAction G₂ W₂]
    (𝒯₁ : SimpleGraph W₁) (𝒯₂ : SimpleGraph W₂) [GraphAction G₁ 𝒯₁] [GraphAction G₂ 𝒯₂]
    (φ : G₁ →* G₂) (hφ : Function.Surjective φ)
    (e : 𝒯₁ ≃g 𝒯₂) (he : ∀ (g : G₁) (w : W₁), e (g • w) = φ g • e w) :
    ∃ (eV : QuotVert G₁ W₁ ≃ QuotVert G₂ W₂) (eE : QuotEdge G₁ 𝒯₁ ≃ QuotEdge G₂ 𝒯₂),
      (∀ w : W₁, eV (Quotient.mk (orbitRel G₁ W₁) w) = Quotient.mk (orbitRel G₂ W₂) (e w)) ∧
      (∀ d : 𝒯₁.Dart,
        eE (Quotient.mk (orbitRel G₁ 𝒯₁.Dart) d) = Quotient.mk (orbitRel G₂ 𝒯₂.Dart) (e.toHom.mapDart d)) ∧
      (∀ x : QuotEdge G₁ 𝒯₁, (quotientDegeneracyData G₂ 𝒯₂).a (eE x) = eV ((quotientDegeneracyData G₁ 𝒯₁).a x)) ∧
      (∀ x : QuotEdge G₁ 𝒯₁, (quotientDegeneracyData G₂ 𝒯₂).b (eE x) = eV ((quotientDegeneracyData G₁ 𝒯₁).b x)) ∧
      (∀ x : QuotEdge G₁ 𝒯₁, quotientReversal G₂ 𝒯₂ (eE x) = eE (quotientReversal G₁ 𝒯₁ x)) ∧
      (∀ d₂ : 𝒯₂.Dart, e.toHom.mapDart (e.symm.toHom.mapDart d₂) = d₂) ∧
      (∀ w : W₁, stabilizer G₂ (e w) = (stabilizer G₁ w).map φ) ∧
      (∀ d : 𝒯₁.Dart, stabilizer G₂ (e.toHom.mapDart d) = (stabilizer G₁ d).map φ) ∧
      (Function.Injective φ → ∀ d : 𝒯₁.Dart,
        Nat.card (stabilizer G₂ (e.toHom.mapDart d)) = Nat.card (stabilizer G₁ d) ∧
        (quotientDegeneracyData G₂ 𝒯₂).w (eE (Quotient.mk (orbitRel G₁ 𝒯₁.Dart) d)) =
          (quotientDegeneracyData G₁ 𝒯₁).w (Quotient.mk (orbitRel G₁ 𝒯₁.Dart) d)) ∧
      (∀ v₁ w : W₁, vertexType 𝒯₂ (e v₁) (e w) = vertexType 𝒯₁ v₁ w) ∧
      (∀ (τ₁ : W₁ → ZMod 2) (τ₂ : W₂ → ZMod 2), (∀ (g : G₁) (w : W₁), τ₁ (g • w) = τ₁ w) →
        (∀ w : W₁, τ₂ (e w) = τ₁ w) →
        (∀ (h : G₂) (w : W₂), τ₂ (h • w) = τ₂ w) ∧
        (∀ x : QuotEdge G₁ 𝒯₁, τ₂ (eE x).out.fst = τ₁ x.out.fst) ∧
        ∃ eEo : {x : QuotEdge G₁ 𝒯₁ // τ₁ x.out.fst = 0} ≃ {y : QuotEdge G₂ 𝒯₂ // τ₂ y.out.fst = 0},
          ∀ x : {x : QuotEdge G₁ 𝒯₁ // τ₁ x.out.fst = 0}, ((eEo x : {y : QuotEdge G₂ 𝒯₂ // τ₂ y.out.fst = 0}) : QuotEdge G₂ 𝒯₂) =
            eE (x : QuotEdge G₁ 𝒯₁)) ∧
      (∀ [DecidableEq (QuotEdge G₁ 𝒯₁)] [DecidableEq (QuotEdge G₂ 𝒯₂)] {E : Type} (orb : E → QuotEdge G₁ 𝒯₁)
        {u v : W₁} (p : 𝒯₁.Walk u v),
        walkCycle 𝒯₂ (fun i => eE (orb i)) (p.map e.toHom) = walkCycle 𝒯₁ orb p) ∧
      (𝒯₁.IsAcyclic → ∀ [DecidableEq (QuotEdge G₁ 𝒯₁)] [DecidableEq (QuotEdge G₂ 𝒯₂)] {E : Type}
        (orb : E → QuotEdge G₁ 𝒯₁) (v₀ : W₁) (g : G₁),
        pathCycle 𝒯₂ (fun i => eE (orb i)) (e v₀) (φ g) = pathCycle 𝒯₁ orb v₀ g) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_exists_quotVert_equiv_quotEdge_equiv_of_iso_of_smul_eq.solution
