import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import P2M.Util
namespace P2MW.S_ModularCurve_XHDRModelAtP_w_preimage_smoothLocus_eq_and_isSeparated_toBase

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    𝔛.w.hom ⁻¹ᵁ 𝔛.smoothLocus = 𝔛.smoothLocus ∧ IsSeparated (toBase p (ΓM M H) hj) := by
  constructor
  ·
    have hle : ∀ (g : X p (ΓM M H) hj ⟶ X p (ΓM M H) hj), g ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj → IsIso g →
        g ⁻¹ᵁ 𝔛.smoothLocus ≤ 𝔛.smoothLocus := by
      intro g hg hiso
      apply 𝔛.smoothLocus_maximal
      have e : (g ⁻¹ᵁ 𝔛.smoothLocus).ι ≫ toBase p (ΓM M H) hj = (g ∣_ 𝔛.smoothLocus) ≫ (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) := by
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hg]
      rw [e]
      haveI : Smooth (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) := SmoothOfRelativeDimension.smooth 1 _
      infer_instance
    have hinv_over : 𝔛.w.inv ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj := by
      rw [Iso.inv_comp_eq, 𝔛.w_over]
    apply le_antisymm (hle 𝔛.w.hom 𝔛.w_over inferInstance)
    calc 𝔛.smoothLocus = (𝔛.w.hom ≫ 𝔛.w.inv) ⁻¹ᵁ 𝔛.smoothLocus := by rw [Iso.hom_inv_id]; rfl
      _ = 𝔛.w.hom ⁻¹ᵁ (𝔛.w.inv ⁻¹ᵁ 𝔛.smoothLocus) := by rw [Scheme.Hom.comp_preimage]
      _ ≤ 𝔛.w.hom ⁻¹ᵁ 𝔛.smoothLocus := Scheme.Hom.preimage_mono _ (hle 𝔛.w.inv hinv_over inferInstance)
  · haveI := 𝔛.isProper
    infer_instance
