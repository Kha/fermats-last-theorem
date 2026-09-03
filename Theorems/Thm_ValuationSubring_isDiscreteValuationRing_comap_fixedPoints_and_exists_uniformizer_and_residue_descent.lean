import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_comap_fixedPoints_and_exists_uniformizer_and_residue_descent

set_option autoImplicit false
namespace ValuationSubring

theorem isDiscreteValuationRing_comap_fixedPoints_and_exists_uniformizer_and_residue_descent
    (K : Type) [Field K] (G : Type) [Group G] [Finite G] [MulSemiringAction G K]
    (W : ValuationSubring K) [IsDiscreteValuationRing W]
    (hfaith : ∀ (g : G) (hg : ∀ x : K, g • x ∈ W ↔ x ∈ W), g ≠ 1 → ∃ x : W,
      (⟨g • (x : K), (hg x).mpr x.2⟩ - x : W) ∉ IsLocalRing.maximalIdeal W) :
    IsDiscreteValuationRing (W.comap (FixedPoints.subfield G K).subtype) ∧
    (∃ π : W.comap (FixedPoints.subfield G K).subtype,
      IsLocalRing.maximalIdeal W =
        Ideal.span {(⟨((π : FixedPoints.subfield G K) : K), π.2⟩ : W)}) ∧
    (∀ w : W,
      (∀ (g : G) (hg : ∀ x : K, g • x ∈ W ↔ x ∈ W),
          (⟨g • (w : K), (hg w).mpr w.2⟩ - w : W) ∈ IsLocalRing.maximalIdeal W) ↔
      ∃ f : W.comap (FixedPoints.subfield G K).subtype,
        w - ⟨((f : FixedPoints.subfield G K) : K), f.2⟩ ∈ IsLocalRing.maximalIdeal W) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_comap_fixedPoints_and_exists_uniformizer_and_residue_descent.solution

end ValuationSubring
