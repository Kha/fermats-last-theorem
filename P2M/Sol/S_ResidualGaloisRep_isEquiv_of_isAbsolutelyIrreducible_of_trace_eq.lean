import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Theorems.Thm_BrauerNesbitt_exists_linearEquiv_of_span_range_eq_top_of_trace_eq
import Definitions.Def_GaloisRep_ResidualEquiv
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import P2M.Util
namespace P2MW.S_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_trace_eq

open Module LinearMap

theorem solution
    {k : Type} [Field k] (ρ₁ ρ₂ : ResidualGaloisRep k)
    (h₁ : ρ₁.IsAbsolutelyIrreducible) (h₂ : ρ₂.IsAbsolutelyIrreducible)
    (htr : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      trace k ρ₁.V (ρ₁.ρ σ) = trace k ρ₂.V (ρ₂.ρ σ)) :
    ρ₁.IsEquiv ρ₂ := by
  haveI : Nontrivial ρ₁.V := Module.nontrivial_of_finrank_pos (R := k) (by rw [ρ₁.finrank_eq]; norm_num)
  obtain ⟨e, he⟩ := BrauerNesbitt.exists_linearEquiv_of_span_range_eq_top_of_trace_eq ρ₁.ρ ρ₂.ρ
    ((ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top ρ₁).mp h₁)
    ((ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top ρ₂).mp h₂) htr
  exact ⟨⟨e, he⟩⟩
