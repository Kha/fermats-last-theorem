import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_natCard_H2_ofMulDistribMulAction_eq_of_valuation

set_option autoImplicit false

open CategoryTheory groupCohomology
theorem groupCohomology.natCard_H2_ofMulDistribMulAction_eq_of_valuation
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    {M : Type} [CommGroup M] [MulDistribMulAction G M]
    (v : M →* Multiplicative ℤ) (hv : Function.Surjective v)
    (hvG : ∀ (g : G) (x : M), v (g • x) = v x)
    (U V : Subgroup M) (hU : ∀ x, x ∈ U ↔ v x = 1) (hVU : V ≤ U)
    (hVG : ∀ (g : G), ∀ x ∈ V, g • x ∈ V) [(V.subgroupOf U).FiniteIndex]
    (hV1 : ∀ f : G → M, (∀ g, f g ∈ V) → IsMulCocycle₁ f → ∃ x ∈ V, ∀ g, g • x / x = f g)
    (hV2 : ∀ f : G × G → M, (∀ p, f p ∈ V) → IsMulCocycle₂ f →
      ∃ x : G → M, (∀ g, x g ∈ V) ∧ ∀ g h, g • x h / x (g * h) * x g = f (g, h))
    (h90 : ∀ f : G → M, IsMulCocycle₁ f → IsMulCoboundary₁ f) :
    Nat.card (H2 (Rep.ofMulDistribMulAction G M)) = Nat.card G := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_natCard_H2_ofMulDistribMulAction_eq_of_valuation.solution
