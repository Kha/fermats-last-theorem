import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq

set_option autoImplicit false

theorem ValuationSubring.exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (ζ : ℕ → L) (hζ : ∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) (hζc : ∀ k, ζ (k + 1) ^ ℓ = ζ k)
    (π : L) (hπ0 : π ≠ 0)
    (σ : L ≃+* L) (hσπ : σ π = π)
    (hσres : ∀ (a : A) (h : σ (a : L) ∈ A), IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a) :
    ∃ t : ℤ_[ℓ], (∀ (k : ℕ) (r : L), r ^ (ℓ ^ k) = π → σ r = ζ k ^ (t.appr k) * r) ∧
      (IsUnit t ↔ ∃ r : L, r ^ ℓ = π ∧ σ r ≠ r) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq.solution
