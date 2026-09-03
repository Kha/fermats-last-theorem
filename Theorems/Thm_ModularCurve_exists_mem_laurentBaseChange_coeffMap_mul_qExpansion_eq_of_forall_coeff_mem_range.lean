import Mathlib
import Definitions.Def_ModularCurve_XH
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) {k : ℤ}
    (Φ Ψ : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k) (hΨ : Ψ ≠ 0)
    (L : Type) [Field L] [CharZero L] (ι : L →+* ℂ)
    (hΦ : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑Φ)).coeff n ∈ Set.range ι)
    (hΨι : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑Ψ)).coeff n ∈ Set.range ι) :
    ∃ x : LaurentSeries L,
      x ∈ ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField N H) ∧
        ModularCurve.coeffMap ι x *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑Ψ)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑Φ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range.solution
