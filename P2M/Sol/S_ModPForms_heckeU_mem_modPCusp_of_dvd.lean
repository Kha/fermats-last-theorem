import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import P2M.Util
namespace P2MW.S_ModPForms_heckeU_mem_modPCusp_of_dvd

set_option autoImplicit false

open scoped MatrixGroups

namespace FltWs24
namespace UStab

theorem T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
  simp [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T]

theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma0 N)]
  exact AddSubgroup.mem_zmultiples 1

theorem heckeU_intCoeff {M : ℕ} {k : ℤ} {ℓ : ℕ} (hℓ : ℓ ≠ 0) (F : Type) [Field F]
    {G : Type*} [FunLike G UpperHalfPlane ℂ] (f : G) [ModularFormClass G (CongruenceSubgroup.Gamma0 M) k]
    (c : ℕ → ℤ) (hc : ∀ n, ModularFormClass.qCoeff f n = (c n : ℂ)) :
    (∀ n, ModularFormClass.qCoeff (ModularForm.heckeU k ℓ ⇑f) n = ((c (n * ℓ) : ℤ) : ℂ)) ∧
    PowerSeries.heckeU ℓ (PowerSeries.mk fun n => ((c n : ℤ) : F)) =
      PowerSeries.mk fun n => ((c (n * ℓ) : ℤ) : F) := by
  refine ⟨fun n => ?_, ?_⟩
  · rw [ModularFormClass.qCoeff_heckeU f (one_mem_strictPeriods_Gamma0 M) hℓ n, ModularForm.coeffHeckeU, hc]
  · ext n
    rw [PowerSeries.coeff_heckeU, PowerSeries.coeff_mk, PowerSeries.coeff_mk, mul_comm]

end FltWs24.UStab

open FltWs24.UStab in
theorem solution (M : ℕ) [NeZero M] (k : ℤ) (ℓ : ℕ) (hℓM : ℓ ∣ M)
    (F : Type) [Field F] (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPCusp M k F) :
    PowerSeries.heckeU ℓ φ ∈ ModPForms.modPCusp M k F := by
  have hℓ : ℓ ≠ 0 := by
    rintro rfl
    exact (NeZero.ne M) (zero_dvd_iff.mp hℓM)
  unfold ModPForms.modPCusp at hφ ⊢
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, c, hc, rfl⟩ := hx
    obtain ⟨he, hps⟩ := heckeU_intCoeff hℓ F f c hc
    rw [hps]
    exact Submodule.subset_span ⟨CuspForm.heckeULin k hℓM f, _, he, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
