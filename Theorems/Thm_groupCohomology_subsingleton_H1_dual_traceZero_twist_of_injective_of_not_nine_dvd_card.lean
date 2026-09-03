import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_subsingleton_H1_dual_traceZero_twist_of_injective_of_not_nine_dvd_card

set_option autoImplicit false

open groupCohomology

theorem groupCohomology.subsingleton_H1_dual_traceZero_twist_of_injective_of_not_nine_dvd_card
    {k : Type} [Field k] [Finite k] [CharP k 3]
    {V : Type} [AddCommGroup V] [Module k V] (hV : Module.finrank k V = 2)
    {Q : Type} [Group Q] [Finite Q] (h9 : ¬ 9 ∣ Nat.card Q)
    (σ : Q →* Module.End k V) (hσ : Function.Injective σ)
    (χ : Q →* (ZMod 3)ˣ)
    [Module (ZMod 3) (LinearMap.ker (LinearMap.trace k V))]
    (A : Rep (ZMod 3) Q)
    (e : A ≃ₗ[ZMod 3] Module.Dual (ZMod 3) (LinearMap.ker (LinearMap.trace k V)))
    (he : ∀ (q : Q) (a : A) (X Y : LinearMap.ker (LinearMap.trace k V)),
      (Y : Module.End k V) = σ q⁻¹ * X * σ q → e (A.ρ q a) X = (χ q : ZMod 3) * e a Y) :
    Subsingleton (H1 A) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_subsingleton_H1_dual_traceZero_twist_of_injective_of_not_nine_dvd_card.solution
