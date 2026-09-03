import Mathlib
import Definitions.Def_LocalLanglands_CartanDecomposition
import P2M.Util
namespace P2MW.S_LocalGL2_cartanDiag_cartanRel_iff

open Matrix LocalGL2

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) {a b a' b' : ℕ}
    (hab : a ≤ b) (hab' : a' ≤ b') :
    LocalGL2.CartanRel (LocalGL2.cartanDiag ϖ a b) (LocalGL2.cartanDiag ϖ a' b')
      ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    have h₁ : a = a' := by
      have hI := h.entryIdeal_eq
      rw [LocalGL2.entryIdeal_cartanDiag ϖ hab, LocalGL2.entryIdeal_cartanDiag ϖ hab',
        Ideal.span_singleton_eq_span_singleton] at hI
      exact (LocalGL2.pow_irreducible_associated_iff hϖ).mp hI
    have h₂ : a + b = a' + b' := by
      have hD := h.det_associated
      rw [LocalGL2.cartanDiag_det, LocalGL2.cartanDiag_det] at hD
      exact (LocalGL2.pow_irreducible_associated_iff hϖ).mp hD
    exact ⟨h₁, by omega⟩
  · rintro ⟨rfl, rfl⟩
    exact LocalGL2.CartanRel.refl _
