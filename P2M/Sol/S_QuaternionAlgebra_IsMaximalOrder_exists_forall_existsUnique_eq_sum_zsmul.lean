import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_forall_existsUnique_eq_sum_zsmul

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    ∃ β : Fin (2 * 2) → ↥Λ, ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j := by
  classical
  have hΛo : IsOrder Λ := hΛ.isOrder
  haveI : Submodule.IsLattice ℚ Λ := ⟨hΛo.fg, hΛo.spanTop⟩
  haveI : Module.Free ℤ ↥Λ := Submodule.IsLattice.free ℚ Λ
  haveI : Module.Finite ℤ ↥Λ := Submodule.IsLattice.finite ℚ Λ
  have h4 : Module.finrank ℤ ↥Λ = 2 * 2 := by
    have hr := Submodule.IsLattice.rank' ℚ Λ
    have : Module.finrank ℤ ↥Λ = Module.finrank ℚ ℍ[ℚ, a, b] := by
      simp only [Module.finrank, hr]
    rw [this, QuaternionAlgebra.finrank_eq_four]
  let B : Module.Basis (Fin (2 * 2)) ℤ ↥Λ := Module.finBasisOfFinrankEq ℤ ↥Λ h4
  refine ⟨B, fun x => ⟨B.equivFun x, ?_, ?_⟩⟩
  · show x = ∑ j, (B.equivFun x) j • B j
    rw [← B.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
  · intro c hc
    have : B.equivFun x = c := by rw [hc, ← B.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
    exact this.symm
