import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_bijective_sum_baseScalar_smul_of_eq_pullbackLocalSection_frame

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.bijective_sum_baseScalar_smul_of_eq_pullbackLocalSection_frame
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (σ' : ((i : Fin g) → ZMod (δ i)) →
      Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol, ⊤))
    (hσ' : ∀ i : Fin (N + 1),
      σ' (e i) =
        (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i) :
          Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
            (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤))) :
    Function.Bijective fun c : ((i : Fin g) → ZMod (δ i)) → S =>
      ∑ h, Polarisation.baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) (c h) • σ' h := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_bijective_sum_baseScalar_smul_of_eq_pullbackLocalSection_frame.solution
