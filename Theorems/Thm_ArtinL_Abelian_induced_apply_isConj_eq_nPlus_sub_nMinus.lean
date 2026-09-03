import Mathlib
import Definitions.Def_ArtinL_Abelian
import P2M.Util
import P2M.Sol.S_ArtinL_Abelian_induced_apply_isConj_eq_nPlus_sub_nMinus

set_option autoImplicit false

open NumberField

universe u

open scoped Classical in

theorem ArtinL.Abelian.induced_apply_isConj_eq_nPlus_sub_nMinus
    {F : Type u} [Field F] [NumberField F] [IsGalois ℚ F]
    (φ : F →+* ℂ) (σ : F ≃ₐ[ℚ] F) (hσ : ComplexEmbedding.IsConj φ σ)
    (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ) :
    (Nat.card H : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F, (if hx : x⁻¹ * σ * x ∈ H then (((χ ⟨x⁻¹ * σ * x, hx⟩ : ℂˣ) : ℂ)) else 0) =
      (ArtinL.Abelian.nPlus (ArtinL.Abelian.ofSubgroup H χ) : ℂ) -
        ArtinL.Abelian.nMinus (ArtinL.Abelian.ofSubgroup H χ) := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_Abelian_induced_apply_isConj_eq_nPlus_sub_nMinus.solution
