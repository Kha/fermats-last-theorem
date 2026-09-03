import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian
import P2M.Util
import P2M.Sol.S_ArtinL_eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
open scoped Classical in

theorem ArtinL.eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F))
    {k : ℕ} (H : Fin k → Subgroup (F ≃ₐ[ℚ] F)) (χ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ)
    (htr : ∀ g : F ≃ₐ[ℚ] F, ((ρF g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
      ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F,
          if hx : x⁻¹ * g * x ∈ H i then (((χ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0))
    {p : ℕ} (hp : p.Prime) :
    ArtinL.eulerFactor ρ p *
        ∏ i, (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (H i))),
            if ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField (H i))) ∈ v.asIdeal then
              (1 - Polynomial.C (ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup (H i) (χ i)) v) *
                Polynomial.X ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal : Polynomial ℂ)
            else 1) ^ (-a i).toNat =
      ∏ i, (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (H i))),
            if ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField (H i))) ∈ v.asIdeal then
              (1 - Polynomial.C (ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup (H i) (χ i)) v) *
                Polynomial.X ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal : Polynomial ℂ)
            else 1) ^ (a i).toNat := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum.solution
