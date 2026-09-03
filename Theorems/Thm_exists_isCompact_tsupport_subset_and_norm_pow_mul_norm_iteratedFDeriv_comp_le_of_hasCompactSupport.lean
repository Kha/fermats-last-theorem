import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import P2M.Util
import P2M.Sol.S_exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport

theorem exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport
    {E E' V P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace P] {f : E' → V} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsupp : HasCompactSupport f)
    {Q : Set P} (hQ : IsCompact Q) {c : P → E'} {ℓ : P → E →L[ℝ] E'}
    (hc : ContinuousOn c Q) (hℓ : ContinuousOn ℓ Q) (hinj : ∀ p ∈ Q, Function.Injective (ℓ p)) :
    (∃ S : Set E, IsCompact S ∧ ∀ p ∈ Q, tsupport (fun x => f (c p + ℓ p x)) ⊆ S) ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ p ∈ Q, ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => f (c p + ℓ p x)) x‖ ≤ C := by p2m_exact_reverting @_root_.P2MW.S_exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport.solution
