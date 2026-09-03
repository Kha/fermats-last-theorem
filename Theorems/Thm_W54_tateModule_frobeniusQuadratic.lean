import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_AttachmentConcrete
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_W54_tateModule_frobeniusQuadratic

open ModularCurve AlgebraicCurve
theorem W54.tateModule_frobeniusQuadratic (M p : ℕ) [NeZero M] :
    letI := ModularCurve.heckeModuleBar M
    ∀ (_h : FrobeniusQuadraticConcrete M p)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (_hℓMp : ¬ ℓ ∣ M * p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (_hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (_hσ : A.IsFrobeniusAt σ ℓ)
    {x : ℕ → JZero M} (_hx : x ∈ TateModule p (JZero M)),
    (fun n => σ • σ • x n - heckeGen ⟨ℓ, hℓ⟩ • (σ • x n) + ℓ • x n) = (0 : ℕ → JZero M) := by p2m_exact_reverting @_root_.P2MW.S_W54_tateModule_frobeniusQuadratic.solution
