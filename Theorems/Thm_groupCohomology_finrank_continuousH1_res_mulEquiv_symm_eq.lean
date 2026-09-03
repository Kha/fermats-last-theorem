import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_Selmer
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_continuousH1_res_mulEquiv_symm_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
universe u
open CategoryTheory groupCohomology
theorem groupCohomology.finrank_continuousH1_res_mulEquiv_symm_eq
    {k G G' : Type u} [Field k] [Group G] [Group G']
    (e : G ≃* G') (r' : G' →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (N : Rep.{u} k G) (χ' : G' →* kˣ) :
    Module.finrank k (Rep.res (e.symm : G' →* G) N).ρ.invariants = Module.finrank k N.ρ.invariants ∧
    Module.finrank k ((Rep.res (e.symm : G' →* G) N).dualTwist χ').ρ.invariants
      = Module.finrank k (N.dualTwist (χ'.comp (e : G →* G'))).ρ.invariants ∧
    Module.finrank k (groupCohomology.continuousH1 r' (Rep.res (e.symm : G' →* G) N))
      = Module.finrank k (groupCohomology.continuousH1 (r'.comp (e : G →* G')) N) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_continuousH1_res_mulEquiv_symm_eq.solution
