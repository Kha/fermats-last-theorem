import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsAffineOpen_isOpen_and_exists_differentiableOn_appLE_of_forall_section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra Topology

theorem AlgebraicGeometry.IsAffineOpen.isOpen_and_exists_differentiableOn_appLE_of_forall_section
    {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of ℂ)) (U : X.Opens) (hU : IsAffineOpen U)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (B : Set E) (hB : IsOpen B) (ψ : E → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) πX)
    (hψU : ∀ v ∈ B, ⊤ ≤ (ψ v).1 ⁻¹ᵁ U)
    (hAN : ∀ s : Γ(X, U), ∃ F : E → ℂ, DifferentiableOn ℂ F B ∧
      ∀ (v : E) (hv : v ∈ B), F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ v).1.appLE U ⊤ (hψU v hv)) s))
    (V : X.Opens) (φ : Γ(X, V)) :
    IsOpen {v : E | v ∈ B ∧ ⊤ ≤ (ψ v).1 ⁻¹ᵁ V} ∧
      ∃ F : E → ℂ, DifferentiableOn ℂ F {v : E | v ∈ B ∧ ⊤ ≤ (ψ v).1 ⁻¹ᵁ V} ∧
        ∀ (v : E) (h : ⊤ ≤ (ψ v).1 ⁻¹ᵁ V), v ∈ B →
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ v).1.appLE V ⊤ h) φ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsAffineOpen_isOpen_and_exists_differentiableOn_appLE_of_forall_section.solution
