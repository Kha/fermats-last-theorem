import Mathlib
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_QAdicPlace
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algHom_slot_mul_qExpansion_slash_eq
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply

open ModularCurve UpperHalfPlane
open scoped MatrixGroups ModularForm
theorem ModularCurve.exists_algHom_slot_mul_qExpansion_slash_eq (N : ℕ) [NeZero N]
    (ζ : ℂˣ) (hζ : (ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N))
    (a b : ℕ) (ha : a ∣ N) (hab : Nat.gcd (Nat.gcd a b) (N / a) = 1) [NeZero a]
    (ι : laurentBaseChange ℂ (modularFunctionFieldFull N) →ₐ[ℂ] LaurentSeries ℂ)
    (hι₁ : ι ⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (jq_mem_full N)⟩ =
        qExpand ℂ N (coeffEmb ℂ jq))
    (hι₂ : ι ⟨coeffEmb ℂ (jqN N), coeffEmb_mem_laurentBaseChange ℂ (jqd_mem_full N (dvd_refl N))⟩ =
        qExpand ℂ (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb ℂ jq))) :
    ∃ σ : SL(2, ℤ), ∀ (x : laurentBaseChange ℂ (modularFunctionFieldFull N)) (k : ℤ)
        (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k),
      (x : LaurentSeries ℂ) * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) →
      ι x * ((qExpansion N ((h : ℍ → ℂ) ∣[k] σ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion N ((g : ℍ → ℂ) ∣[k] σ) : PowerSeries ℂ) : LaurentSeries ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algHom_slot_mul_qExpansion_slash_eq.solution
