import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularEquationQ
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_modularFunctionFieldC_apply_jGeomGen_eq_comp
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply

set_option autoImplicit false

theorem ModularCurve.exists_algEquiv_modularFunctionFieldC_apply_jGeomGen_eq_comp
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (κ k : Type) [Field κ] [CharP κ p] [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k]
    (τ : κ →+* k)
    (θ θ₀ : ↥(ModularCurve.modularFunctionFieldC κ M) →+* ↥(ModularCurve.modularFunctionFieldC k M))
    (hθκ : ∀ c : κ, θ (algebraMap κ _ c) = algebraMap k _ (τ c))
    (hθ₀κ : ∀ c : κ, θ₀ (algebraMap κ _ c) = algebraMap k _ (τ c))
    (hθj : θ (ModularCurve.jGeomGen κ M) = ModularCurve.jGeomGen k M)
    (hθ₀j : θ₀ (ModularCurve.jGeomGen κ M) = ModularCurve.jGeomGen k M) :
    ∃ α : ↥(ModularCurve.modularFunctionFieldC k M) ≃ₐ[k] ↥(ModularCurve.modularFunctionFieldC k M),
      α (ModularCurve.jGeomGen k M) = ModularCurve.jGeomGen k M ∧ ∀ f, θ f = α (θ₀ f) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_modularFunctionFieldC_apply_jGeomGen_eq_comp.solution
