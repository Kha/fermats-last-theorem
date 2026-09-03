import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology

theorem AlgebraicGeometry.IsClosedImmersion.exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE
    {X Y : Scheme.{0}} (g : X ⟶ Y) [IsClosedImmersion g]
    (π : (Fin 2 → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ X)) (v₀ : Fin 2 → ℂ)

    (hcont : ∀ W : X.Opens, ⊤ ≤ (π v₀) ⁻¹ᵁ W → ∃ ε' : ℝ, 0 < ε' ∧ ∀ v ∈ Metric.ball v₀ ε', ⊤ ≤ (π v) ⁻¹ᵁ W)

    (U : X.Opens) (f₁ f₂ : Γ(X, U)) (ε : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ)) (F : (Fin 2 → ℂ) → (Fin 2 → ℂ))
    (hε : 0 < ε) (hU : ∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (π v) ⁻¹ᵁ U)
    (hF : ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ (π v) ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
      F v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v).appLE U ⊤ h) f₁), (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v).appLE U ⊤ h) f₂)])
    (hD : HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀) :
    ∃ (V : Y.Opens) (f₂' f₃' : Γ(Y, V)) (ε' : ℝ) (F' : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
      0 < ε' ∧
      (∀ v ∈ Metric.ball v₀ ε', ⊤ ≤ (π v ≫ g) ⁻¹ᵁ V) ∧
      (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ (π v ≫ g) ⁻¹ᵁ V), v ∈ Metric.ball v₀ ε' →
        F' v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v ≫ g).appLE V ⊤ h) f₂'), (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v ≫ g).appLE V ⊤ h) f₃')]) ∧
      HasFDerivAt F' (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE.solution
