import Definitions.Def_LatticeTreeBaseChange
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_unitOrbitalCount_eq_one_of_anisotropic_and_eq_two_of_eisenstein_of_depth_zero
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

open scoped Matrix

theorem LT.LatticeTree.unitOrbitalCount_eq_one_of_anisotropic_and_eq_two_of_eisenstein_of_depth_zero
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] :
    (∀ (Y : Matrix (Fin 2) (Fin 2) R) (b : R) (g : Matrix.GeneralLinearGroup (Fin 2) K),
      (∀ (a : R ⧸ Ideal.span {ϖ}) (w : Fin 2 → R ⧸ Ideal.span {ϖ}),
        (Y.map (Ideal.Quotient.mk (Ideal.span {ϖ}) : R →+* R ⧸ Ideal.span {ϖ})) *ᵥ w = a • w → w = 0) →
      IsUnit (b • (1 : Matrix (Fin 2) (Fin 2) R) + Y).det →
      (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K b • 1 + Y.map (algebraMap R K) →
      LT.LatticeTree.unitOrbitalCount R g = 1) ∧
    (∀ (Y : Matrix (Fin 2) (Fin 2) R) (w : Rˣ) (b : R) (g : Matrix.GeneralLinearGroup (Fin 2) K),
      Y.det = ϖ * (w : R) → ϖ ∣ Y.trace →
      IsUnit (b • (1 : Matrix (Fin 2) (Fin 2) R) + Y).det →
      (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K b • 1 + Y.map (algebraMap R K) →
      LT.LatticeTree.unitOrbitalCount R g = 2) := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_unitOrbitalCount_eq_one_of_anisotropic_and_eq_two_of_eisenstein_of_depth_zero.solution
