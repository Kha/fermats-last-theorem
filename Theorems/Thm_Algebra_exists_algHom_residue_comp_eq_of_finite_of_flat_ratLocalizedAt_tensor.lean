import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_Algebra_exists_algHom_residue_comp_eq_of_finite_of_flat_ratLocalizedAt_tensor
attribute [-instance] ValuationSubring.instIsAlgClosedResidueField
attribute [-simp] ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply

open scoped TensorProduct

theorem Algebra.exists_algHom_residue_comp_eq_of_finite_of_flat_ratLocalizedAt_tensor
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (H : Type) [CommRing H] [Algebra ℤ H]
    (hfin : Module.Finite ↥(GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt ℓ) H))
    (hflat : Module.Flat ℤ H)
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime ℓ)
    (χ : H →ₐ[ℤ] IsLocalRing.ResidueField ↥B) :
    ∃ φ : H →ₐ[ℤ] ↥B, ∀ h : H, χ h = IsLocalRing.residue ↥B (φ h) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_algHom_residue_comp_eq_of_finite_of_flat_ratLocalizedAt_tensor.solution
