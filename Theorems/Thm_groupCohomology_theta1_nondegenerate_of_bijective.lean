import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import P2M.Util
import P2M.Sol.S_groupCohomology_theta1_nondegenerate_of_bijective
set_option autoImplicit false
open Module
universe u
theorem groupCohomology.theta1_nondegenerate_of_bijective {k G : Type u} [Group G] [Field k]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M D : Rep.{u} k G}
    (θ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D))
    (hbij : Function.Bijective θ) :
    (∀ x : continuousH1 r M, (∀ w : continuousH1 r D, θ x w = 0) → x = 0)
    ∧ ∀ w : continuousH1 r D, (∀ x : continuousH1 r M, θ x w = 0) → w = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_theta1_nondegenerate_of_bijective.solution
