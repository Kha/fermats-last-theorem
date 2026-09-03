import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one
import P2M.Util
namespace P2MW.S_LT_LatticeTree_card_orbitalBall_sdiff_of_act_swap_of_isWithin_one
set_option autoImplicit false

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (x₀ x₁ : LT.LatticeTree.Vertex R K)
    (hadj : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁)
    (hne : x₀ ≠ x₁) (h₀ : LT.LatticeTree.Vertex.act g x₀ = x₁) (h₁ : LT.LatticeTree.Vertex.act g x₁ = x₀) :
    LT.LatticeTree.fixedVertexSet (R := R) g = ∅ ∧
    (∀ r : ℕ,
        LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 2) g \
          LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g = ∅) ∧
    ∀ r : ℕ,
      (LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g \
          LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r) g).Finite ∧
      Nat.card
        ↥(LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g \
            LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r) g) =
        2 * Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by
  have h := LT.LatticeTree.card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one R K ϖ hϖ
    (LT.LatticeTree.IntegralAut.refl R K) g x₀ x₁ hadj hne
    (by rw [LT.LatticeTree.Vertex.twistedAct_refl]; exact h₀)
    (by rw [LT.LatticeTree.Vertex.twistedAct_refl]; exact h₁)
  simp only [LT.LatticeTree.twistedFixedVertexSet_refl, LT.LatticeTree.twistedOrbitalBall_refl] at h
  exact h
