import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_of_isPullback_of_isPullback

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.Iso.of_isPullback_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X₁ X₂ : PolarisedAbelianScheme 2 d m S} {X₁' X₂' : PolarisedAbelianScheme 2 d m S'}
    {t₁ : QMStructure Λ star β X₁} {t₂ : QMStructure Λ star β X₂}
    {t₁' : QMStructure Λ star β X₁'} {t₂' : QMStructure Λ star β X₂'}
    (h : QMStructure.Iso t₁ t₂) (h₁ : QMStructure.IsPullback φ t₁ t₁') (h₂ : QMStructure.IsPullback φ t₂ t₂') :
    QMStructure.Iso t₁' t₂' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_of_isPullback_of_isPullback.solution
