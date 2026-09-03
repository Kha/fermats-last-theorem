import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_forall_gammaSpecIso_appLE_specMap_comp_eq_div_pow

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_forall_gammaSpecIso_appLE_specMap_comp_eq_div_pow
    {K : Type u} [Field K] {S : Type u} [CommRing S] [Algebra K S]
    {Y : Scheme.{u}} (P : Spec (CommRingCat.of S) ⟶ Y) (V : Y.Opens) (φ : Γ(Y, V))
    (σ₁ : S →ₐ[K] K) (h₁ : ⊤ ≤ (Spec.map (CommRingCat.ofHom σ₁.toRingHom) ≫ P) ⁻¹ᵁ V) :
    ∃ (s₀ a : S) (k : ℕ), σ₁ s₀ ≠ 0 ∧
      ∀ σ : S →ₐ[K] K, σ s₀ ≠ 0 →
        ∃ h : ⊤ ≤ (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ P) ⁻¹ᵁ V,
          (Scheme.ΓSpecIso (CommRingCat.of K)).hom
              (((Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ P).appLE V ⊤ h) φ) = σ a / σ s₀ ^ k := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_forall_gammaSpecIso_appLE_specMap_comp_eq_div_pow.solution
