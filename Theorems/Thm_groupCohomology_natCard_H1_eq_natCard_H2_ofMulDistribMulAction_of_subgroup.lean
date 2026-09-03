import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_natCard_H1_eq_natCard_H2_ofMulDistribMulAction_of_subgroup

set_option autoImplicit false

open CategoryTheory groupCohomology
theorem groupCohomology.natCard_H1_eq_natCard_H2_ofMulDistribMulAction_of_subgroup {G : Type} [Group G] [Finite G] [IsCyclic G]
    {M : Type} [CommGroup M] [MulDistribMulAction G M]
    (U V : Subgroup M) (hVU : V ≤ U) (hUG : ∀ (g : G), ∀ x ∈ U, g • x ∈ U)
    (hVG : ∀ (g : G), ∀ x ∈ V, g • x ∈ V) [(V.subgroupOf U).FiniteIndex]
    (hV1 : ∀ f : G → M, (∀ g, f g ∈ V) → IsMulCocycle₁ f → ∃ x ∈ V, ∀ g, g • x / x = f g)
    (hV2 : ∀ f : G × G → M, (∀ p, f p ∈ V) → IsMulCocycle₂ f →
      ∃ x : G → M, (∀ g, x g ∈ V) ∧ ∀ g h, g • x h / x (g * h) * x g = f (g, h))
    [MulDistribMulAction G U] (hcompatU : ∀ (g : G) (u : U), ((g • u : U) : M) = g • (u : M)) :
    Finite (H1 (Rep.ofMulDistribMulAction G U)) ∧ Finite (H2 (Rep.ofMulDistribMulAction G U)) ∧
      Nat.card (H1 (Rep.ofMulDistribMulAction G U)) = Nat.card (H2 (Rep.ofMulDistribMulAction G U)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_natCard_H1_eq_natCard_H2_ofMulDistribMulAction_of_subgroup.solution
