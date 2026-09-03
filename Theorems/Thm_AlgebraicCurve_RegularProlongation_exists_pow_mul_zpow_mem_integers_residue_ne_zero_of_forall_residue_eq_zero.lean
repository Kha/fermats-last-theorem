import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv AlgebraicClosure.Rat.isGalois
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero
    (A : ValuationSubring (AlgebraicClosure ℚ)) (F : Type*) [Field F] [Algebra (AlgebraicClosure ℚ) F]
    (Fbar : Type*) [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (u : F) (hu0 : u ≠ 0) (hu : ∀ h : u ∈ R.integers, R.residue ⟨u, h⟩ = 0)
    (f : F) (hf : f ≠ 0) :
    ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧ ∃ h : f ^ m * u ^ j ∈ R.integers, R.residue ⟨f ^ m * u ^ j, h⟩ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero.solution
