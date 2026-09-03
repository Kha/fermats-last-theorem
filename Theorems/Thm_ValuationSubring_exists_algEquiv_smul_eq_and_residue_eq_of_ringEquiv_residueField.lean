import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq

open scoped Pointwise in
theorem ValuationSubring.exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField (p : ℕ) [Fact p.Prime] (A A' : ValuationSubring (AlgebraicClosure ℚ)) [CharP (IsLocalRing.ResidueField A) p] (e : IsLocalRing.ResidueField A' ≃+* IsLocalRing.ResidueField A) : ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ • A' = A ∧ ∀ (x : A') (y : A), (y : AlgebraicClosure ℚ) = τ (x : AlgebraicClosure ℚ) → IsLocalRing.residue A y = e (IsLocalRing.residue A' x) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField.solution
