import Definitions.Def_LatticeTreeBaseChange
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

open scoped Matrix

theorem LT.LatticeTree.unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] :
    (∀ (Y : Matrix (Fin 2) (Fin 2) R),
      (∀ (a : R ⧸ Ideal.span {ϖ}) (w : Fin 2 → R ⧸ Ideal.span {ϖ}),
        (Y.map (Ideal.Quotient.mk (Ideal.span {ϖ}) : R →+* R ⧸ Ideal.span {ϖ})) *ᵥ w = a • w → w = 0) →
      ∀ (m : ℕ) (a : R) (g : Matrix.GeneralLinearGroup (Fin 2) K),
      (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K a • 1 + algebraMap R K ϖ ^ m • Y.map (algebraMap R K) →
      IsUnit (a • (1 : Matrix (Fin 2) (Fin 2) R) + ϖ ^ m • Y).det →
      (Nat.card (R ⧸ Ideal.span {ϖ}) - 1) * LT.LatticeTree.unitOrbitalCount R g + 2 =
        (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ m) ∧
    (∀ (Y : Matrix (Fin 2) (Fin 2) R) (w : Rˣ), Y.det = ϖ * (w : R) → ϖ ∣ Y.trace →
      ∀ (m : ℕ) (a : R) (g : Matrix.GeneralLinearGroup (Fin 2) K),
      (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K a • 1 + algebraMap R K ϖ ^ m • Y.map (algebraMap R K) →
      IsUnit (a • (1 : Matrix (Fin 2) (Fin 2) R) + ϖ ^ m • Y).det →
      (Nat.card (R ⧸ Ideal.span {ϖ}) - 1) * LT.LatticeTree.unitOrbitalCount R g + 2 =
        2 * Nat.card (R ⧸ Ideal.span {ϖ}) ^ (m + 1)) := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth.solution
