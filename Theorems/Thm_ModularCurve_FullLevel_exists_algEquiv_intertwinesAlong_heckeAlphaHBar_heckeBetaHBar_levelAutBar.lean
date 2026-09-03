import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel AlgebraicCurve

open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') (ℓ : ℕ) [NeZero ℓ] (hqℓ : ¬ q ∣ ℓ)
    (hβ : ModularCurve.HeckeBetaHDefined (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') ℓ)
    (ζ : ModularCurve.FullLevel.Idx q) (x x' : SL(2, ℤ)) (hx' : x' ∈ CongruenceSubgroup.Gamma0 M')
    (h : !![(ℓ : ℤ), 0; 0, 1] * (x : Matrix (Fin 2) (Fin 2) ℤ) =
      (x' : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1]) :
    ∃ τ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')
              (q ^ 2 * M' * ℓ))) ≃ₐ[AlgebraicClosure ℚ]
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')
              (q ^ 2 * M' * ℓ))),
      AlgebraicCurve.SemilinearAut.IntertwinesAlong
          (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (q ^ 2 * M')
            (ModularCurve.FullLevel.levelH q M') ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.FullLevel.levelAutBar q M' ζ x))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) ∧
        AlgebraicCurve.SemilinearAut.IntertwinesAlong
          (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (q ^ 2 * M')
            (ModularCurve.FullLevel.levelH q M') ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.FullLevel.levelAutBar q M' ζ x'))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar.solution
