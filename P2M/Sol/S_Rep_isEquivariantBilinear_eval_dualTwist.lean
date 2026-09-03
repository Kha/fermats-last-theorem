import Mathlib
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_CupProduct
import P2M.Util
namespace P2MW.S_Rep_isEquivariantBilinear_eval_dualTwist

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory

theorem solution {k G : Type u} [Field k] [Group G]
    (M : Rep.{u} k G) (χ : G →* kˣ) :
    Rep.IsEquivariantBilinear M (M.dualTwist χ) (groupCohomology.ofChar χ)
      (Module.Dual.eval k M : M →ₗ[k] M.dualTwist χ →ₗ[k] groupCohomology.ofChar χ) := by
  intro g m f
  show ((M.dualTwist χ).ρ g f) (M.ρ g m) = (groupCohomology.ofChar χ).ρ g (f m)
  rw [Rep.dualTwist_ρ_apply, LinearMap.smul_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel, map_one, Module.End.one_apply]
  show (χ g : k) • f m = ((Representation.trivial k G k).twist χ) g (f m)
  rw [Representation.twist_apply_apply]
  simp
