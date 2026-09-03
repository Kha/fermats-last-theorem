import Mathlib
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_CupProduct
import P2M.Util
import P2M.Sol.S_Rep_isEquivariantBilinear_eval_dualTwist

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.isEquivariantBilinear_eval_dualTwist {k G : Type u} [Field k] [Group G]
    (M : Rep.{u} k G) (χ : G →* kˣ) :
    Rep.IsEquivariantBilinear M (M.dualTwist χ) (groupCohomology.ofChar χ)
      (Module.Dual.eval k M : M →ₗ[k] M.dualTwist χ →ₗ[k] groupCohomology.ofChar χ) := by p2m_exact_reverting @_root_.P2MW.S_Rep_isEquivariantBilinear_eval_dualTwist.solution
