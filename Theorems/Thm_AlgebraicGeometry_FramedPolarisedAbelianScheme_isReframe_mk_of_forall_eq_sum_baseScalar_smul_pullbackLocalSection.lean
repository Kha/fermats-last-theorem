import Definitions.Def_AlgebraicGeometry_ThetaReframe
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isReframe_mk_of_forall_eq_sum_baseScalar_smul_pullbackLocalSection

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.isReframe_mk_of_forall_eq_sum_baseScalar_smul_pullbackLocalSection
    {g N n : ℕ} {δ : Fin g → ℕ} [hδ : ∀ i, NeZero (δ i)] (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (P : Scheme.Modules.ProjPresentation X.pol X.f N) (h₁ : IsClosedImmersion P.toProj)
    (h₂ : Scheme.Modules.IsSectionBasis X.f X.pol P.σ)
    (τ τ' : ((i : Fin g) → ZMod (δ i)) →
      Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol, ⊤))
    (hτ : ∀ i : Fin (N + 1), τ (e i) =
      (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i) :
        Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
          (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤)))
    (hτ' : ∀ i : Fin (N + 1), τ' (e i) =
      (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (P.σ i) :
        Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
          (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤)))
    (W : Matrix (Fin (N + 1)) (Fin (N + 1)) S)
    (hW : ∀ i : Fin (N + 1), τ' (e i) =
      ∑ j : Fin (N + 1), Polarisation.baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) (W i j) • τ (e j)) :
    X.IsReframe W ⟨X.toPolarisedAbelianScheme, P, h₁, h₂⟩ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isReframe_mk_of_forall_eq_sum_baseScalar_smul_pullbackLocalSection.solution
