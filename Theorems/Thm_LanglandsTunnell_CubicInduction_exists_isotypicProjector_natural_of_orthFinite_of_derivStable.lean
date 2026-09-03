import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_isotypicProjector_natural_of_orthFinite_of_derivStable

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_isotypicProjector_natural_of_orthFinite_of_derivStable
    (X : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (hD : (∀ w ∈ X, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ X))
    (hK : (∀ w ∈ X, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ X))
    (hfin : ∀ w ∈ X, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (hcont : ∀ w ∈ X, Continuous w) (hsm : ∀ w ∈ X, WhittakerBlock.IsArchSmooth3 w)
    (B : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ)
    (hB : (∀ w ∈ X, ∀ w' ∈ X, B w' w = (starRingEnd ℂ) (B w w')) ∧
        (∀ (z : ℂ), ∀ w₁ ∈ X, ∀ w₂ ∈ X, ∀ w' ∈ X, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') ∧
        (∀ w ∈ X, w ≠ 0 → 0 < (B w w).re) ∧
        (∀ w ∈ X, ∀ w' ∈ X, ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w')) ∧
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ X, ∀ w' ∈ X, B (fun g => w (g * k)) (fun g => w' (g * k)) = B w w')
    (a : ℕ) (ha : a = 0 ∨ a = 1) (ℓ : ℕ) (hℓ : ℓ = 0 ∨ ℓ = 1) :
    ∃ P : ↥X →ₗ[ℂ] ↥X,
      (∀ u : ↥X, ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈
        Submodule.span ℂ {w | ∃ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) ∧ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
            w = fun g => (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g * k)}) ∧
      (∀ u : ↥X, P (P u) = P u) ∧
      (∀ u w : ↥X, B (P u) w = B u (P w)) ∧
      (∀ (Φ : ↥X →ₗ[ℂ] ((Fin 3 → Fin 3 → ℝ) → ℂ)),
        (∀ (u : ↥X) (r : Fin 3 → Fin 3 → ℝ) (hr : (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0))
            (k : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1)
            (hk₂ : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3),
            k = WhittakerBlock.archRealLift3 r →
            ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
              Φ ⟨fun g => (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g * k), hK u u.2 k hk₁ hk₂⟩ o =
                Φ u (fun i j => ∑ k : Fin 3, o i k * r k j)) →
        (∀ u : ↥X,
          ((ℓ = 0 ∧ (∀ o r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
            Φ u (fun i j => ∑ k : Fin 3, o i k * r k j) = (Matrix.of fun i j : Fin 3 => ((r i j : ℝ) : ℂ)).det ^ a * Φ u o)) ∨
           (ℓ = 1 ∧ (∃ c : Fin 3 → Fin 3 → ℂ, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
            Φ u o = (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ a * ∑ i : Fin 3, ∑ j : Fin 3, c i j * ((o i j : ℝ) : ℂ)))) →
          ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → Φ (P u) o = Φ u o)) ∧
      (∀ u : ↥X, ((ℓ = 0 ∧ ∀ i j : Fin 3, WhittakerBlock.archDeriv i j ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv j i ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = 0) ∨
           (ℓ = 1 ∧ (WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 0 1 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 1 0 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) - WhittakerBlock.archDeriv 1 0 (WhittakerBlock.archDeriv 0 1 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 1 0 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) +
            (WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 0 2 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 2 0 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) - WhittakerBlock.archDeriv 2 0 (WhittakerBlock.archDeriv 0 2 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 2 0 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) +
            (WhittakerBlock.archDeriv 1 2 (WhittakerBlock.archDeriv 1 2 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 2 1 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) - WhittakerBlock.archDeriv 2 1 (WhittakerBlock.archDeriv 1 2 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 2 1 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) + (2 : ℂ) • ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = 0))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_isotypicProjector_natural_of_orthFinite_of_derivStable.solution
