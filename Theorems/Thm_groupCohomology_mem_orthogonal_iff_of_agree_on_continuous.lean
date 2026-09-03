import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import P2M.Util
import P2M.Sol.S_groupCohomology_mem_orthogonal_iff_of_agree_on_continuous
set_option autoImplicit false
open Module
universe u
theorem groupCohomology.mem_orthogonal_iff_of_agree_on_continuous {k G : Type u} [Group G] [Field k]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M M' : Rep.{u} k G}
    (pairing : H1 M →ₗ[k] H1 M' →ₗ[k] k)
    (θ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r M'))
    (hagree : ∀ (x : continuousH1 r M) (w : continuousH1 r M'),
      pairing x w = θ x w)
    (L : Submodule k (H1 M)) (hL : L ≤ continuousH1 r M)
    (w : continuousH1 r M') :
    (w : H1 M') ∈ orthogonal pairing L ↔ ∀ x : H1 M, ∀ hx : x ∈ L, θ ⟨x, hL hx⟩ w = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_mem_orthogonal_iff_of_agree_on_continuous.solution
