import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_span_eq_top_forall_exists_bijective_and_apply_eq_of_comp_eq_smul_comp

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_span_eq_top_forall_exists_bijective_and_apply_eq_of_comp_eq_smul_comp
    {R : Type u} [CommRing R]
    {H : Type v} [AddCommGroup H] [Fintype H]
    {H' : Type w} [AddCommGroup H'] [Fintype H']
    (hcard : Fintype.card H' = Fintype.card H) (hd : IsUnit ((Fintype.card H : ℕ) : R))
    (e : H → H' → Rˣ)
    (he₁ : ∀ (h₁ h₂ : H) (χ : H'), e (h₁ + h₂) χ = e h₁ χ * e h₂ χ)
    (he₂ : ∀ (h : H) (χ₁ χ₂ : H'), e h (χ₁ + χ₂) = e h χ₁ * e h χ₂)
    (hsep : ∀ h : H, h ≠ 0 → ∃ χ : H', IsUnit ((e h χ : R) - 1))
    (hsep' : ∀ χ : H', χ ≠ 0 → ∃ h : H, IsUnit ((e h χ : R) - 1))
    {M : Type u} [AddCommGroup M] [Module R M]
    {ι : Type u} [Fintype ι] (b : Module.Basis ι R M) (hrank : Fintype.card ι = Fintype.card H)
    (U : H → M →ₗ[R] M) (hU0 : U 0 = LinearMap.id) (hU : ∀ h₁ h₂ : H, U (h₁ + h₂) = U h₁ ∘ₗ U h₂)
    (V : H' → M →ₗ[R] M) (hV0 : V 0 = LinearMap.id) (hV : ∀ χ₁ χ₂ : H', V (χ₁ + χ₂) = V χ₁ ∘ₗ V χ₂)
    (hHeis : ∀ (h : H) (χ : H'), V χ ∘ₗ U h = (e h χ : R) • (U h ∘ₗ V χ)) :
    ∃ (n : ℕ) (r : Fin n → R), Ideal.span (Set.range r) = ⊤ ∧
      ∀ (j : Fin n) (Rj : Type u) [CommRing Rj] [Algebra R Rj] [IsLocalization.Away (r j) Rj]
        (Mj : Type u) [AddCommGroup Mj] [Module R Mj] [Module Rj Mj] [IsScalarTower R Rj Mj]
        (ℓ : M →ₗ[R] Mj) [IsLocalizedModule (Submonoid.powers (r j)) ℓ]
        (U' : H → Mj →ₗ[Rj] Mj) (_hU' : ∀ (h : H) (m : M), U' h (ℓ m) = ℓ (U h m))
        (V' : H' → Mj →ₗ[Rj] Mj) (_hV' : ∀ (χ : H') (m : M), V' χ (ℓ m) = ℓ (V χ m)),
        ∃ σ : H → Mj,
          Function.Bijective (fun c : H → Rj => ∑ h, c h • σ h) ∧
          (∀ k h : H, U' k (σ h) = σ (k + h)) ∧
          (∀ (χ : H') (h : H), V' χ (σ h) = algebraMap R Rj (e h χ : R) • σ h) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_span_eq_top_forall_exists_bijective_and_apply_eq_of_comp_eq_smul_comp.solution
