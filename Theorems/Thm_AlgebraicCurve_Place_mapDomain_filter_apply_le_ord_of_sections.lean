import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_mapDomain_filter_apply_le_ord_of_sections

set_option autoImplicit false

open AlgebraicCurve

open Classical in

theorem AlgebraicCurve.Place.mapDomain_filter_apply_le_ord_of_sections
    {K F : Type*} [Field K] [Field F] [Algebra K F] {k E : Type*} [Field k] [Field E] [Algebra k E]
    (𝒪 : ValuationSubring F) (ρ : 𝒪 →+* E)
    (hker : ∀ x : 𝒪, ρ x ≠ 0 → IsUnit x)
    (r : Place K F → Place k E) (S : Place K F → Prop) (v : Place k E)
    (hE : ∀ (f : F) (h : f ∈ 𝒪), (∀ W, S W → r W = v → 0 ≤ W.ord f) → 0 ≤ v.ord (ρ ⟨f, h⟩))
    (hP : ∀ Q, S Q → r Q = v → ∃ (s : F) (hs : s ∈ 𝒪),
      Q.ord s = 1 ∧ (∀ W, S W → r W = v → W ≠ Q → W.ord s = 0) ∧ v.ord (ρ ⟨s, hs⟩) = 1)
    (f : F) (h : f ∈ 𝒪) (hr : ρ ⟨f, h⟩ ≠ 0)
    (D : Divisor K F) (hD : ∀ W, D W = W.ord f)
    (hreg : ∀ W, S W → r W = v → 0 ≤ D W) :
    Finsupp.mapDomain r (D.filter S) v ≤ v.ord (ρ ⟨f, h⟩) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_mapDomain_filter_apply_le_ord_of_sections.solution
