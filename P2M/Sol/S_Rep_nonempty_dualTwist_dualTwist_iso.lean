import Mathlib
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
namespace P2MW.S_Rep_nonempty_dualTwist_dualTwist_iso

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

set_option maxHeartbeats 3200000 in

theorem solution
    {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ] (χ : Γ →* (ZMod p)ˣ)
    (M : Rep (ZMod p) Γ) [FiniteDimensional (ZMod p) M] :
    Nonempty ((M.dualTwist χ).dualTwist χ ≅ M) := by
  classical

  have key : ∀ (g : Γ) (m : M),
      ((M.dualTwist χ).dualTwist χ).ρ g (Module.Dual.eval (ZMod p) M m) = Module.Dual.eval (ZMod p) M (M.ρ g m) := by
    intro g m
    apply LinearMap.ext
    intro f
    rw [Rep.dualTwist_ρ_apply, LinearMap.smul_apply, LinearMap.comp_apply, Rep.dualTwist_ρ_apply,
      Module.Dual.eval_apply, Module.Dual.eval_apply, LinearMap.smul_apply, LinearMap.comp_apply, inv_inv,
      smul_smul, map_inv, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  let e : Module.Dual (ZMod p) (Module.Dual (ZMod p) M) ≃ₗ[ZMod p] M := (Module.evalEquiv (ZMod p) M).symm
  have h : ∀ g : Γ, (e : _ →ₗ[ZMod p] M) ∘ₗ ((M.dualTwist χ).dualTwist χ).ρ g = M.ρ g ∘ₗ (e : _ →ₗ[ZMod p] M) := by
    intro g
    apply LinearMap.ext
    intro φ
    obtain ⟨m, rfl⟩ := (Module.evalEquiv (ZMod p) M).surjective φ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e]
    rw [Module.evalEquiv_apply, key, ← Module.evalEquiv_apply, ← Module.evalEquiv_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact ⟨Rep.mkIso (Representation.Equiv.mk e h)⟩
