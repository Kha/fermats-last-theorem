import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LatticeTreeBaseChange
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Pointwise

theorem
LT.LatticeTree.card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) (γ : GL (Fin 2) (v.adicCompletion K))
    (b : ℤ) (n : ℕ) (hn : 1 ≤ n) (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (2 * b + (n : ℤ)))
    (dl : GL (Fin 2) (v.adicCompletion K))
    (hdl : (dl : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal
        ![algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (b + (n : ℤ)),
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ b])
    (Tc : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hTc : ∀ t : GL (Fin 2) (v.adicCompletion K),
      t ∈ Tc ↔ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
        ∃ w : (v.adicCompletionIntegers K)ˣ,
          Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
            algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) w)
    (St : GL (Fin 2) (v.adicCompletion K) → Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hSt : ∀ s t : GL (Fin 2) (v.adicCompletion K),
      t ∈ St s ↔ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
        s⁻¹ * t * s ∈ AutomorphicForm.localIntegralSet K v)
    (S : Finset (GL (Fin 2) (v.adicCompletion K)))
    (hSsupp : ∀ s ∈ S,
      s⁻¹ * γ * s ∈
        AutomorphicForm.localIntegralSet K v *
            ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
          AutomorphicForm.localIntegralSet K v)
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∀ u ∈ AutomorphicForm.localIntegralSet K v, s' = t * s * u → s' = s)
    (hcov :
      ∀ x : GL (Fin 2) (v.adicCompletion K),
        x⁻¹ * γ * x ∈
          AutomorphicForm.localIntegralSet K v *
              ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
            AutomorphicForm.localIntegralSet K v →
        ∃ s ∈ S,
          ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
            ∃ u ∈ AutomorphicForm.localIntegralSet K v, x = t * s * u) :
    Nat.card
        ↥(LT.LatticeTree.orbitalBall (R := v.adicCompletionIntegers K)
            (LT.LatticeTree.unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero) n γ \
          LT.LatticeTree.orbitalBall (R := v.adicCompletionIntegers K)
            (LT.LatticeTree.unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero) (n - 1) γ) =
      (Tc ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) *
        ∑ s ∈ S, (St s).relIndex Tc := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow.solution
