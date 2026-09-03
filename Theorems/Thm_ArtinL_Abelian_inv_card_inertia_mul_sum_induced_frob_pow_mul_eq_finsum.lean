import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open scoped Pointwise Classical
open IsDedekindDomain

theorem ArtinL.Abelian.inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ) {p : ℕ} (hp : p.Prime)
    (P : Ideal (𝓞 F)) [P.IsMaximal] [P.LiesOver (Ideal.span {(p : ℤ)})] {j : ℕ} (hj : 0 < j) :
    (Fintype.card ↥(P.inertia (F ≃ₐ[ℚ] F)) : ℂ)⁻¹ *
        ∑ τ : ↥(P.inertia (F ≃ₐ[ℚ] F)), ((Nat.card ↥H : ℂ)⁻¹ *
          ∑ x : F ≃ₐ[ℚ] F,
            if hx : x⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * (τ : F ≃ₐ[ℚ] F)) * x ∈ H then
              ((χ ⟨x⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * (τ : F ≃ₐ[ℚ] F)) * x, hx⟩ : ℂˣ) : ℂ)
            else 0) =
      ∑ᶠ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
        if ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField H)) ∈ v.asIdeal ∧
            (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∣ j then
          ((Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal : ℂ) *
            ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup H χ) v ^
              (j / (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal)
        else 0 := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum.solution
