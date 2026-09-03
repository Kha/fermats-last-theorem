import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_tendsto_forall_eq_of_injOn_of_differentiableOn_appLE_of_tendsto_appLE

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra Filter Topology

theorem AlgebraicGeometry.exists_tendsto_forall_eq_of_injOn_of_differentiableOn_appLE_of_tendsto_appLE
    (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of ℂ)) (hsm : SmoothOfRelativeDimension 1 g)
    (W : Set UpperHalfPlane) (hW : IsOpen W)
    (h : UpperHalfPlane → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g) (hinj : Set.InjOn h W)

    (hHOL : ∀ (U : Y.Opens) (s : Γ(Y, U)),
      IsOpen {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧ ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U} ∧
      ∃ F : ℂ → ℂ,
        DifferentiableOn ℂ F
          {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧ ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U} ∧
        ∀ (z : ℂ), 0 < z.im → UpperHalfPlane.ofComplex z ∈ W →
          ∀ hU : ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U,
            F z = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((h (UpperHalfPlane.ofComplex z)).1.appLE U ⊤ hU) s))
    (τs : UpperHalfPlane) (hτs : τs ∈ W)

    (σ : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g)
    (hconv : ∀ (U : Y.Opens), IsAffineOpen U → ∀ (hQ : ⊤ ≤ (h τs).1 ⁻¹ᵁ U),
      ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (σ n).1 ⁻¹ᵁ U,
        ∀ f : Γ(Y, U),
          Tendsto (fun n : ℕ => if hn : n₀ ≤ n then
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((σ n).1.appLE U ⊤ (hP n hn)) f) else 0)
            atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((h τs).1.appLE U ⊤ hQ) f)))) :
    ∃ (τ' : ℕ → UpperHalfPlane) (n₀ : ℕ), (∀ n, n₀ ≤ n → τ' n ∈ W ∧ h (τ' n) = σ n) ∧
      Tendsto τ' atTop (𝓝 τs) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_tendsto_forall_eq_of_injOn_of_differentiableOn_appLE_of_tendsto_appLE.solution
