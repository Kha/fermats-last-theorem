import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_tendsto_appLE_of_tendsto_appLE_of_isAffineOpen_complex

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Filter Topology

theorem AlgebraicGeometry.tendsto_appLE_of_tendsto_appLE_of_isAffineOpen_complex
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of ℂ)}
    (P : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)
    (U₀ : X.Opens) (hU₀ : IsAffineOpen U₀) (hQ₀ : ⊤ ≤ Q.1 ⁻¹ᵁ U₀) (n₀ : ℕ) (hP₀ : ∀ n, n₀ ≤ n → ⊤ ≤ (P n).1 ⁻¹ᵁ U₀)
    (h₀ : ∀ s : Γ(X, U₀),
      Tendsto (fun n : ℕ => if h : n₀ ≤ n then
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P n).1.appLE U₀ ⊤ (hP₀ n h)) s) else 0)
        atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U₀ ⊤ hQ₀) s)))) :
    ∀ (U : X.Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ Q.1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (P n).1 ⁻¹ᵁ U,
          ∀ s : Γ(X, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P n).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U ⊤ hx) s))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_tendsto_appLE_of_tendsto_appLE_of_isAffineOpen_complex.solution
