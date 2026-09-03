import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_AttachmentConcrete
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_W54_tateModule_adicContinuity

open ModularCurve AlgebraicCurve
theorem W54.tateModule_adicContinuity (M p : ℕ) [NeZero M] :
    letI := ModularCurve.heckeModuleBar M
    ∀ (_h : ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ L ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
          ∀ v : JZero M,
            v ∈ Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar M) (p ^ n) →
            σ • v = v),
    ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ L ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
          ∀ x ∈ TateModule p (JZero M), ∃ y ∈ TateModule p (JZero M),
            (p ^ n : ℕ) • y = (fun m => σ • x m) - x := by p2m_exact_reverting @_root_.P2MW.S_W54_tateModule_adicContinuity.solution
