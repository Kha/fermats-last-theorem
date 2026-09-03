import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    (F : ↥(upperHalfPlane K₀ K) → K)
    (hinv : ∀ (γ : G) (z w : ↥(upperHalfPlane K₀ K)), (w : K) = pmoebius K₀ (ρ γ) (z : K) → F w = F z)
    (γ : G) (m n : ℕ) (p : ↥(upperHalfPlane K₀ K)) (hp : (p : K) ∈ affinoid ϖ m)
    (s : K) (hs : s ≠ 0)
    (hE : ∀ w : K, Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s → w ∈ affinoid ϖ n)
    {φ : ↥{w : K | Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s} → K}
    (hφ : φ ∈ holOn K {w : K | Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s}) (e : ℕ)
    (he : e = 0 ∨ φ ⟨pmoebius K₀ (ρ γ) (p : K), by simp⟩ ≠ 0)
    (h : ∀ w : ↥{w : K | Valued.v (w - pmoebius K₀ (ρ γ) (p : K)) ≤ Valued.v s},
      (w : K) ≠ pmoebius K₀ (ρ γ) (p : K) →
      ((w : K) - pmoebius K₀ (ρ γ) (p : K)) ^ e *
          F ⟨(w : K), affinoid_subset_upperHalfPlane ϖ n (hE (w : K) w.2)⟩ = φ w) :
    ∃ r : K, r ≠ 0 ∧ ∃ hD : (∀ z : K, Valued.v (z - (p : K)) ≤ Valued.v r → z ∈ affinoid ϖ m),
      ∃ φ' : ↥{z : K | Valued.v (z - (p : K)) ≤ Valued.v r} → K,
        φ' ∈ holOn K {z : K | Valued.v (z - (p : K)) ≤ Valued.v r} ∧
        (e = 0 ∨ φ' ⟨(p : K), by simp⟩ ≠ 0) ∧
        ∀ z : ↥{z : K | Valued.v (z - (p : K)) ≤ Valued.v r}, (z : K) ≠ (p : K) →
          ((z : K) - (p : K)) ^ e *
              F ⟨(z : K), affinoid_subset_upperHalfPlane ϖ m (hD (z : K) z.2)⟩ = φ' z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc.solution
