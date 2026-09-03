import Definitions.Def_TaylorWiles_Primes
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Normal.Defs
import P2M.Util
import P2M.Sol.S_NumberField_exists_isFrobenius_lift_arithFrobAt
attribute [-instance] AlgebraicClosure.Rat.isGalois

open scoped NumberField Pointwise
theorem NumberField.exists_isFrobenius_lift_arithFrobAt
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField E] [IsGalois ℚ E]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)]
    [Finite (𝓞 E ⧸ Q)] :
    ∃ (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) (_ : Qt.IsMaximal)
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      Qt.LiesOver Q ∧ AlgEquiv.restrictNormal τ E = arithFrobAt ℤ (E ≃ₐ[ℚ] E) Q ∧
      (∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x ∈ Qt ↔ x ∈ Qt) ∧
      ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x - x ^ ℓ ∈ Qt := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_isFrobenius_lift_arithFrobAt.solution
