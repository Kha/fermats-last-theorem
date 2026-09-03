import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_IsPullback_trans

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.IsPullback.trans
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (χ : S' →+* S'')
    {X : PolarisedAbelianScheme 2 d m S} {X' : PolarisedAbelianScheme 2 d m S'} {X'' : PolarisedAbelianScheme 2 d m S''}
    {t : QMStructure Λ star β X} {t' : QMStructure Λ star β X'} {t'' : QMStructure Λ star β X''}
    (h : QMStructure.IsPullback φ t t') (h' : QMStructure.IsPullback χ t' t'') :
    QMStructure.IsPullback (χ.comp φ) t t'' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_IsPullback_trans.solution
