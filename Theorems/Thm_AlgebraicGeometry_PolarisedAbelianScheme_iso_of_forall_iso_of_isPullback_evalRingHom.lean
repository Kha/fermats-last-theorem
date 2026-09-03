import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_forall_iso_of_isPullback_evalRingHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.iso_of_forall_iso_of_isPullback_evalRingHom
    {g d n : ℕ} {k : ℕ} (R : Fin k → Type) [∀ i, CommRing (R i)]
    (w₁ w₂ : PolarisedAbelianScheme g d n (∀ i, R i))
    (v₁ v₂ : ∀ i, PolarisedAbelianScheme g d n (R i))
    (h₁ : ∀ i, PolarisedAbelianScheme.IsPullback (Pi.evalRingHom R i) w₁ (v₁ i))
    (h₂ : ∀ i, PolarisedAbelianScheme.IsPullback (Pi.evalRingHom R i) w₂ (v₂ i))
    (h : ∀ i, PolarisedAbelianScheme.Iso (v₁ i) (v₂ i)) :
    PolarisedAbelianScheme.Iso w₁ w₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_forall_iso_of_isPullback_evalRingHom.solution
