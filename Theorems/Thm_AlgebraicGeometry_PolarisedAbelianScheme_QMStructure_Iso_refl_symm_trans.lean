import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_refl_symm_trans

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.Iso.refl_symm_trans
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ}
    {d m : ℕ} {S : Type} [CommRing S] :
    (∀ (X : PolarisedAbelianScheme 2 d m S) (t : QMStructure Λ star β X), QMStructure.Iso t t) ∧
    (∀ (X Y : PolarisedAbelianScheme 2 d m S) (t : QMStructure Λ star β X) (u : QMStructure Λ star β Y),
      QMStructure.Iso t u → QMStructure.Iso u t) ∧
    (∀ (X Y W : PolarisedAbelianScheme 2 d m S) (t : QMStructure Λ star β X) (u : QMStructure Λ star β Y)
      (w : QMStructure Λ star β W), QMStructure.Iso t u → QMStructure.Iso u w → QMStructure.Iso t w) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_refl_symm_trans.solution
