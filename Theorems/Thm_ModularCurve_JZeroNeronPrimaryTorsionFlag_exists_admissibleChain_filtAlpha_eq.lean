import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
import Definitions.Def_MazurAdmissible_GaloisModule
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_admissibleChain_filtAlpha_eq
open ModularCurve AlgebraicCurve MazurAdmissible AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring
theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_admissibleChain_filtAlpha_eq (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p) (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m)
    (Φ : letI := heckeModuleBar p
      OpenAction ↥(eisensteinPrimaryTorsionBar p q m))
    (hΦ : letI := heckeModuleBar p
      ∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))
        (x : ↥(eisensteinPrimaryTorsionBar p q m)),
        (Φ.φ σ x : JZero p) = σ • (x : JZero p)) :
    letI := heckeModuleBar p
    ∃ c : AdmissibleChain q Φ,
      filtAlpha c = (Finset.univ.filter (fun i => flag.kind i = JZeroFlagLayerKind.const)).card ∧
      filtLength c = flag.n := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_admissibleChain_filtAlpha_eq.solution
