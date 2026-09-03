import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Theorems.Thm_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import P2M.Util
namespace P2MW.S_ModularCurve_exists_algEquiv_x1FunctionFieldBar_coe_eq_coeffMap_of_algEquiv_laurentBaseChange
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one

set_option autoImplicit false

open scoped MatrixGroups

theorem solution
    (N : ℕ) [NeZero N]
    (L : Type) [Field L] [CharZero L] [Algebra L (AlgebraicClosure ℚ)]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    (σ : ↥K ≃ₐ[L] ↥K) :
    ∃ σbar : ↥(ModularCurve.x1FunctionFieldBar N) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar N),
      ∀ (f : ↥(ModularCurve.x1FunctionFieldBar N)) (b : ↥K),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
        ((σbar f : ↥(ModularCurve.x1FunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((σ b : ↥K) : LaurentSeries L) := by
  classical

  have hL : K = ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma1 N) := by
    rw [hK]
    exact ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq L (CongruenceSubgroup.Gamma1 N)
  have hB : ModularCurve.x1FunctionFieldBar N =
      ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 N) :=
    ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 N)

  let eL := IntermediateField.equivOfEq hL
  let eB := IntermediateField.equivOfEq hB
  let σ₀ : ↥(ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma1 N)) ≃ₐ[L]
      ↥(ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma1 N)) :=
    (eL.symm.trans σ).trans eL
  obtain ⟨τ, hτ, -⟩ :=
    ModularCurve.existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap
      (algebraMap L (AlgebraicClosure ℚ)) (CongruenceSubgroup.Gamma1 N) σ₀
  refine ⟨(eB.trans τ).trans eB.symm, fun f b hfb => ?_⟩

  have h0 : ((eB f : ↥(ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 N))) :
      LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ))
        ((eL b : ↥(ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma1 N))) : LaurentSeries L) := by
    exact hfb
  have h1 := hτ (eL b) (eB f) h0
  have h3 : ((σ₀ (eL b) : ↥(ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma1 N))) : LaurentSeries L) =
      ((σ b : ↥K) : LaurentSeries L) := by
    show ((eL (σ (eL.symm (eL b))) : ↥(ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma1 N))) :
      LaurentSeries L) = ((σ b : ↥K) : LaurentSeries L)
    rw [AlgEquiv.symm_apply_apply]
    rfl
  have h2 : ((((eB.trans τ).trans eB.symm) f : ↥(ModularCurve.x1FunctionFieldBar N)) :
      LaurentSeries (AlgebraicClosure ℚ)) =
      ((τ (eB f) : ↥(ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 N))) :
        LaurentSeries (AlgebraicClosure ℚ)) := rfl
  rw [h3] at h1
  exact h2.trans h1
