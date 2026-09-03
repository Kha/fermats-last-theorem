import Mathlib
import Definitions.Def_GroupCohomology_Selmer
import P2M.Util
import P2M.Sol.S_groupCohomology_H1pi_dualTwist_adjointTraceZero_eq_zero_of_finite_range
attribute [-simp] ModularCurve.upperElem_zero ModularCurve.lowerElem_coe ModularCurve.lowerElem_zero ModularCurve.upperElem_coe

set_option autoImplicit false

open groupCohomology

theorem groupCohomology.H1pi_dualTwist_adjointTraceZero_eq_zero_of_finite_range
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    {V : Type} [AddCommGroup V] [Module k V] (hV : Module.finrank k V = 2)
    {G : Type} [Group G] (ρ : G →* Module.End k V) (hfin : (Set.range ρ).Finite)
    (χ : G →* (ZMod p)ˣ) (hχ : Function.Surjective χ)
    (hirr : ∀ W : Submodule k V,
      (∀ g : G, χ g = 1 → ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    [Module (ZMod p) (LinearMap.ker (LinearMap.trace k V))]
    (ρ₀ : Representation (ZMod p) G (LinearMap.ker (LinearMap.trace k V)))
    (hρ₀ : ∀ (g : G) (f : LinearMap.ker (LinearMap.trace k V)),
      ((ρ₀ g f : LinearMap.ker (LinearMap.trace k V)) : Module.End k V) = ρ g * f * ρ g⁻¹)
    (hχ₀ : ∀ g : G, ρ₀ g = 1 → χ g = 1)
    (c : cocycles₁ ((Rep.of ρ₀).dualTwist χ))
    (hc : ∀ g : G, ρ₀ g = 1 → c g = 0) :
    H1π ((Rep.of ρ₀).dualTwist χ) c = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_H1pi_dualTwist_adjointTraceZero_eq_zero_of_finite_range.solution
