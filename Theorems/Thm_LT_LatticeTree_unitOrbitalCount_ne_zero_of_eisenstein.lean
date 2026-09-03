import Definitions.Def_LatticeTreeOrbital
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_unitOrbitalCount_ne_zero_of_eisenstein
attribute [-simp] LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

theorem LT.LatticeTree.unitOrbitalCount_ne_zero_of_eisenstein
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (d : ℕ) (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : Rˣ) (Y : Matrix (Fin 2) (Fin 2) R)
    (hY : ∀ i j,
      (γ : Matrix (Fin 2) (Fin 2) R) i j = (mu : R) * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    (w : Rˣ) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R)) (htr : ϖ ∣ Y 0 0 + Y 1 1) :
    LT.LatticeTree.unitOrbitalCount R (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_unitOrbitalCount_ne_zero_of_eisenstein.solution
