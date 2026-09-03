import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty
import P2M.Util
namespace P2MW.S_LT_LatticeTree_card_orbitalBall_sdiff_of_finite_fixedVertexSet_of_nonempty
set_option autoImplicit false

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hfin : (LT.LatticeTree.fixedVertexSet (R := R) g).Finite)
    (hne : (LT.LatticeTree.fixedVertexSet (R := R) g).Nonempty) :
    (∀ r : ℕ,
        LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g \
          LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r) g = ∅) ∧
    ∀ r : ℕ,
      (LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 2) g \
          LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g).Finite ∧
      Nat.card
        ↥(LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 2) g \
            LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g) =
        (LT.LatticeTree.unitOrbitalCount R g * (Nat.card (R ⧸ Ideal.span {ϖ}) - 1) + 2) *
          Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by
  have h := LT.LatticeTree.card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty R K ϖ hϖ
    (LT.LatticeTree.IntegralAut.refl R K) g
    (by rw [LT.LatticeTree.twistedFixedVertexSet_refl]; exact hfin)
    (by rw [LT.LatticeTree.twistedFixedVertexSet_refl]; exact hne)
  simp only [LT.LatticeTree.twistedOrbitalBall_refl, LT.LatticeTree.twistedUnitOrbitalCount_refl] at h
  exact h
