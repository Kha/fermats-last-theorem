import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_hom_isPullback_opensInclusion_of_forall_affineOpens_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_hom_isPullback_opensInclusion_of_forall_affineOpens_isPullback
    (M : Scheme.{u}) (Z : M.affineOpens → Scheme.{u}) (q : ∀ U : M.affineOpens, Z U ⟶ (U.1 : Scheme.{u}))
    (ρ : ∀ {U V : M.affineOpens}, U ≤ V → (Z U ⟶ Z V))
    (ρ_id : ∀ U : M.affineOpens, ρ (le_refl U) = 𝟙 (Z U))
    (ρ_comp : ∀ {U V W : M.affineOpens} (h₁ : U ≤ V) (h₂ : V ≤ W), ρ h₁ ≫ ρ h₂ = ρ (h₁.trans h₂))
    (hsq : ∀ {U V : M.affineOpens} (h : U ≤ V), IsPullback (ρ h) (q U) (q V) (M.homOfLE h)) :
    ∃ (X : Scheme.{u}) (f : X ⟶ M) (ι : ∀ U : M.affineOpens, Z U ⟶ X),
      (∀ U, IsOpenImmersion (ι U)) ∧
      (∀ U, IsPullback (q U) (ι U) U.1.ι f) ∧
      (∀ {U V : M.affineOpens} (h : U ≤ V), ρ h ≫ ι V = ι U) ∧
      (∀ x : X, ∃ (U : M.affineOpens) (y : Z U), (ι U).base y = x) ∧
      ∀ (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P], (∀ U, P (q U)) → P f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_hom_isPullback_opensInclusion_of_forall_affineOpens_isPullback.solution
