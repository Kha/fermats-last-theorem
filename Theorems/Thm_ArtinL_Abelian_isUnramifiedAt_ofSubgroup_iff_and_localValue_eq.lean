import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_isUnramifiedAt_ofSubgroup_iff_and_localValue_eq

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open scoped Pointwise Classical
open IsDedekindDomain

theorem ArtinL.Abelian.isUnramifiedAt_ofSubgroup_iff_and_localValue_eq
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ) {p : ℕ} (hp : p.Prime)
    (Q : Ideal (𝓞 F)) [Q.IsMaximal] [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)))
    (hv : Q.under (𝓞 ↥(IntermediateField.fixedField H)) = v.asIdeal) :
    (ArtinL.Abelian.IsUnramifiedAt (ArtinL.Abelian.ofSubgroup H χ) v ↔
        ∀ (σ : F ≃ₐ[ℚ] F) (hσ : σ ∈ H), σ ∈ Q.inertia (F ≃ₐ[ℚ] F) → χ ⟨σ, hσ⟩ = 1) ∧
    (ArtinL.Abelian.IsUnramifiedAt (ArtinL.Abelian.ofSubgroup H χ) v →
        ∀ (σ : F ≃ₐ[ℚ] F) (hσ : σ ∈ H),
          σ⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∈
              Q.inertia (F ≃ₐ[ℚ] F) →
            ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup H χ) v = ((χ ⟨σ, hσ⟩ : ℂˣ) : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_isUnramifiedAt_ofSubgroup_iff_and_localValue_eq.solution
