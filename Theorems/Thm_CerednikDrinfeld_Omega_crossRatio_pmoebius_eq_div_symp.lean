import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_crossRatio_pmoebius_eq_div_symp

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.crossRatio_pmoebius_eq_div_symp
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    (g₁ g₂ g₃ g₄ : GL (Fin 2) K₀) {w₁ w₂ w₃ w₄ : K}
    (hw₁ : w₁ ∈ upperHalfPlane K₀ K) (hw₂ : w₂ ∈ upperHalfPlane K₀ K)
    (hw₃ : w₃ ∈ upperHalfPlane K₀ K) (hw₄ : w₄ ∈ upperHalfPlane K₀ K) :
    let P : GL (Fin 2) K₀ → K → Fin 2 → K := fun g w =>
      ![algebraMap K₀ K (g 0 0) * w + algebraMap K₀ K (g 0 1), algebraMap K₀ K (g 1 0) * w + algebraMap K₀ K (g 1 1)]
    crossRatio (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₁) w₁) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₂) w₂)
        (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₃) w₃) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₄) w₄) =
      ((P g₁ w₁ 0 * P g₃ w₃ 1 - P g₁ w₁ 1 * P g₃ w₃ 0) * (P g₂ w₂ 0 * P g₄ w₄ 1 - P g₂ w₂ 1 * P g₄ w₄ 0)) /
      ((P g₁ w₁ 0 * P g₄ w₄ 1 - P g₁ w₁ 1 * P g₄ w₄ 0) * (P g₂ w₂ 0 * P g₃ w₃ 1 - P g₂ w₂ 1 * P g₃ w₃ 0)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_crossRatio_pmoebius_eq_div_symp.solution
