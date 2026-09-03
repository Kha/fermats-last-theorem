import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_groupCohomology_nonempty_continuous_linearEquiv_of_mulEquiv

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.nonempty_continuous_linearEquiv_of_mulEquiv {k G H : Type u} [CommRing k] [Group G] [Group H]
    (rG : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (rH : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (e : G ≃* H) (he : ∀ g, rH (e g) = rG g) (NG : Rep.{u} k G) (NH : Rep.{u} k H)
    (φ : NG ≃ₗ[k] NH) (hφ : ∀ (g : G) (x : NG), φ (NG.ρ g x) = NH.ρ (e g) (φ x)) :
    Nonempty (NG.ρ.invariants ≃ₗ[k] NH.ρ.invariants) ∧
    Nonempty (groupCohomology.continuousH1 rG NG ≃ₗ[k] groupCohomology.continuousH1 rH NH) ∧
    Nonempty (groupCohomology.continuousH2 rG NG ≃ₗ[k] groupCohomology.continuousH2 rH NH) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_nonempty_continuous_linearEquiv_of_mulEquiv.solution
