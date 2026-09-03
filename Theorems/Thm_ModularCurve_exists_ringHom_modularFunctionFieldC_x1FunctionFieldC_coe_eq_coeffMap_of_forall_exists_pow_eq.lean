import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (κ k : Type) [Field κ] [CharP κ p] [Field k] [CharP k p] [IsAlgClosed k]
    (halg : ∀ x : k, ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x)
    (τ : κ →+* k)
    (hincl : ModularCurve.modularFunctionFieldC κ M ≤ ModularCurve.x1FunctionFieldC κ M)
    (hfin : letI := (IntermediateField.inclusion hincl).toRingHom.toAlgebra;
      FiniteDimensional ↥(ModularCurve.modularFunctionFieldC κ M) ↥(ModularCurve.x1FunctionFieldC κ M) ∧
      Algebra.IsSeparable ↥(ModularCurve.modularFunctionFieldC κ M) ↥(ModularCurve.x1FunctionFieldC κ M)) :
    ∃ (Lθ : ↥(ModularCurve.modularFunctionFieldC κ M) →+* ↥(ModularCurve.modularFunctionFieldC k M))
      (Lφ : ↥(ModularCurve.x1FunctionFieldC κ M) →+* ↥(ModularCurve.x1FunctionFieldC k M))
      (hincl' : ModularCurve.modularFunctionFieldC k M ≤ ModularCurve.x1FunctionFieldC k M),
      (∀ f, ((Lθ f : ↥(ModularCurve.modularFunctionFieldC k M)) : LaurentSeries k) =
        ModularCurve.coeffMap τ ((f : ↥(ModularCurve.modularFunctionFieldC κ M)) : LaurentSeries κ)) ∧
      (∀ f, ((Lφ f : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) =
        ModularCurve.coeffMap τ ((f : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ)) ∧
      (∀ c : κ, Lθ (algebraMap κ _ c) = algebraMap k _ (τ c)) ∧
      (∀ c : κ, Lφ (algebraMap κ _ c) = algebraMap k _ (τ c)) ∧
      Lθ (ModularCurve.jGeomGen κ M) = ModularCurve.jGeomGen k M ∧
      Lθ (ModularCurve.jNGeomGen κ M) = ModularCurve.jNGeomGen k M ∧
      Algebra.adjoin k (Set.range Lθ) = ⊤ ∧ Algebra.adjoin k (Set.range Lφ) = ⊤ ∧
      (letI := (IntermediateField.inclusion hincl').toRingHom.toAlgebra;
        FiniteDimensional ↥(ModularCurve.modularFunctionFieldC k M) ↥(ModularCurve.x1FunctionFieldC k M) ∧
        Algebra.IsSeparable ↥(ModularCurve.modularFunctionFieldC k M) ↥(ModularCurve.x1FunctionFieldC k M)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq.solution
