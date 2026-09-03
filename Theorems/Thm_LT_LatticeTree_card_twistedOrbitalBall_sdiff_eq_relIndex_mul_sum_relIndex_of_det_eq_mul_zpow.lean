import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_LatticeTreeBaseChange
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_card_twistedOrbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow

set_option autoImplicit false

open scoped Pointwise

theorem
LT.LatticeTree.card_twistedOrbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (σ : LT.LatticeTree.IntegralAut R K)
    (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] (hσϖ : σ.toBase ϖ = ϖ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (b : ℤ) (n : ℕ) (hn : 1 ≤ n) (u : Rˣ)
    (hdet : Matrix.det (δ : Matrix (Fin 2) (Fin 2) K) =
      algebraMap R K u *
        algebraMap R K ϖ ^ (2 * b + (n : ℤ)))
    (dl : Matrix.GeneralLinearGroup (Fin 2) K)
    (hdl : (dl : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal
        ![algebraMap R K ϖ ^ (b + (n : ℤ)),
          algebraMap R K ϖ ^ b])
    (Tc : Subgroup (Matrix.GeneralLinearGroup (Fin 2) K))
    (hTc : ∀ t : Matrix.GeneralLinearGroup (Fin 2) K,
      t ∈ Tc ↔ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ ∧
        ∃ w : Rˣ, Matrix.det (t : Matrix (Fin 2) (Fin 2) K) = algebraMap R K w)
    (St : Matrix.GeneralLinearGroup (Fin 2) K → Subgroup (Matrix.GeneralLinearGroup (Fin 2) K))
    (hSt : ∀ s t : Matrix.GeneralLinearGroup (Fin 2) K,
      t ∈ St s ↔ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ ∧
        s⁻¹ * t * s ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)))
    (S : Finset (Matrix.GeneralLinearGroup (Fin 2) K))
    (hSsupp : ∀ s ∈ S,
      s⁻¹ * δ * σ.mapGL s ∈
        AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) *
            ({dl} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) *
          AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)))
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ,
          ∀ u ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)), s' = t * s * u → s' = s)
    (hcov :
      ∀ x : Matrix.GeneralLinearGroup (Fin 2) K,
        x⁻¹ * δ * σ.mapGL x ∈
          AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) *
              ({dl} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) *
            AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) →
        ∃ s ∈ S,
          ∃ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ,
            ∃ u ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)), x = t * s * u) :
    Nat.card
        ↥(LT.LatticeTree.twistedOrbitalBall
            (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n δ σ \
          LT.LatticeTree.twistedOrbitalBall
            (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n - 1) δ σ) =
      (Tc ⊔ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K)).relIndex
          (AutomorphicForm.sigmaCentralizer σ.mapGL δ) *
        ∑ s ∈ S, (St s).relIndex Tc := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_card_twistedOrbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow.solution
