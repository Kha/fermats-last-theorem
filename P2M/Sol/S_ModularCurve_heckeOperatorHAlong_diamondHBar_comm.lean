import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Theorems.Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul
import P2M.Util
namespace P2MW.S_ModularCurve_heckeOperatorHAlong_diamondHBar_comm
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.SemilinearAut ModularCurve

theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime] (d : (ZMod M)ˣ) (P : ModularCurve.JH M H) :
    ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ (ModularCurve.diamondHBar M H d P) =
      ModularCurve.diamondHBar M H d
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ P) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  rw [diamondHBar_apply, diamondHBar_apply]
  by_cases h : HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ
  · obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := h
    rw [heckeOperatorHAlong_eq h0 hα hβ hFI hfin hN]
    obtain ⟨τ, hτα, hτβ⟩ := exists_algEquiv_intertwinesAlong_diamondAutHBar M H ℓ d
    exact SemilinearAut.pic0_correspondence_smul (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ)
      (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hβ hα hFI hfin hN hτβ hτα P
  · rw [heckeOperatorHAlong_of_not h]
    simp
