import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_crossRatio_pmoebius_pmoebius_sub_one_eq

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.crossRatio_pmoebius_pmoebius_sub_one_eq
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    (g : GL (Fin 2) K₀) {a b : K} (z z₀ : K)
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hΦ : (z * (algebraMap K₀ K (g 1 0) * b + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * b + algebraMap K₀ K (g 0 1))) ≠ 0)
    (hΦ₀ : (z₀ * (algebraMap K₀ K (g 1 0) * a + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * a + algebraMap K₀ K (g 0 1))) ≠ 0) :
    crossRatio z z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) a) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) b) - 1 =
      (z - z₀) * (a - b) * algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀)) /
        ((z * (algebraMap K₀ K (g 1 0) * b + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * b + algebraMap K₀ K (g 0 1))) *
          (z₀ * (algebraMap K₀ K (g 1 0) * a + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * a + algebraMap K₀ K (g 0 1)))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_crossRatio_pmoebius_pmoebius_sub_one_eq.solution
