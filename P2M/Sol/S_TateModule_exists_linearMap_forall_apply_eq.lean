import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
namespace P2MW.S_TateModule_exists_linearMap_forall_apply_eq

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime] (M M' : Type) [AddCommGroup M] [AddCommGroup M'] (φ : M →+ M') :
    ∃ T : TateModule p M →ₗ[ℤ_[p]] TateModule p M',
      ∀ (x : TateModule p M) (n : ℕ), ((T x : TateModule p M') : ℕ → M') n = φ ((x : ℕ → M) n) := by
  refine ⟨{ toFun := fun x => ⟨fun n => φ ((x : ℕ → M) n), fun n => ⟨?_, ?_⟩⟩,
            map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · rw [← map_zsmul, TateModule.torsion, map_zero]
  · rw [← map_zsmul, TateModule.compat]
  · intro x y
    exact Subtype.ext (funext fun n => by
      show φ (((x + y : TateModule p M) : ℕ → M) n) = φ ((x : ℕ → M) n) + φ ((y : ℕ → M) n)
      rw [TateModule.coe_add, Pi.add_apply, map_add])
  · intro a x
    exact Subtype.ext (funext fun n => by
      show φ ((((a • x : TateModule p M)) : ℕ → M) n) = ((a.appr n : ℕ) : ℤ) • φ ((x : ℕ → M) n)
      rw [TateModule.smul_apply, map_zsmul])
  · intro x n; rfl
