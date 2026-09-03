import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_maximalIdeal_comap_fixedPoints_eq_span_and_mem_iff_exists_invariant_of_isLocalization

set_option autoImplicit false
namespace ValuationSubring

theorem maximalIdeal_comap_fixedPoints_eq_span_and_mem_iff_exists_invariant_of_isLocalization
    (K : Type) [Field K] (G : Type) [Group G] [Finite G] [MulSemiringAction G K]
    (W : ValuationSubring K) [IsDiscreteValuationRing W]

    (π : K) (hπG : ∀ g : G, g • π = π) (hπW : π ∈ W)
    (hπ : IsLocalRing.maximalIdeal W = Ideal.span {(⟨π, hπW⟩ : W)})

    (hfaith : ∀ (g : G) (hg : ∀ x : K, g • x ∈ W ↔ x ∈ W), g ≠ 1 → ∃ x : W,
      (⟨g • (x : K), (hg x).mpr x.2⟩ - x : W) ∉ IsLocalRing.maximalIdeal W)

    (B : Subring K) (hBG : ∀ (g : G) (b : K), b ∈ B → g • b ∈ B) (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (hloc : ∀ f : K, f ∈ W ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧
      (∀ hh : h ∈ W, (⟨h, hh⟩ : W) ∉ IsLocalRing.maximalIdeal W) ∧ f * h = g) :

    IsDiscreteValuationRing (W.comap (FixedPoints.subfield G K).subtype) ∧

    (∃ hπ0 : (⟨π, fun g => hπG g⟩ : FixedPoints.subfield G K) ∈ W.comap (FixedPoints.subfield G K).subtype,
      IsLocalRing.maximalIdeal (W.comap (FixedPoints.subfield G K).subtype) = Ideal.span {(⟨_, hπ0⟩ : W.comap (FixedPoints.subfield G K).subtype)}) ∧

    (∀ f : K, (∀ g : G, g • f = f) →
      (f ∈ W ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ σ : G, σ • g = g) ∧ (∀ σ : G, σ • h = h) ∧
        (∀ hh : h ∈ W, (⟨h, hh⟩ : W) ∉ IsLocalRing.maximalIdeal W) ∧ f * h = g)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_maximalIdeal_comap_fixedPoints_eq_span_and_mem_iff_exists_invariant_of_isLocalization.solution

end ValuationSubring
