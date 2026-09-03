import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_FibreModel
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPModel_FibreModel_exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.NodeLocalized ModularCurve.CharPModel

theorem ModularCurve.CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    (fm : CharPModel.FibreModel N A q k red) (b : fm.BFin) :
    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K₀),
      ∀ K : IntermediateField ℚ (AlgebraicClosure ℚ), K₀ ≤ K →
        ((heckeAlphaBar (AlgebraicClosure ℚ) N q (b : ↥(modularFunctionFieldBar N)) : ↥(modularFunctionFieldBar (N * q))) :
            LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K ∧
        ((heckeBetaBar (AlgebraicClosure ℚ) N q (b : ↥(modularFunctionFieldBar N)) : ↥(modularFunctionFieldBar (N * q))) :
            LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPModel_FibreModel_exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem.solution
