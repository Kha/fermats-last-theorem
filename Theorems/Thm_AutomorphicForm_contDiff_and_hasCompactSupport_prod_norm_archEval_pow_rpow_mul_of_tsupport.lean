import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_contDiff_and_hasCompactSupport_prod_norm_archEval_pow_rpow_mul_of_tsupport

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem AutomorphicForm.contDiff_and_hasCompactSupport_prod_norm_archEval_pow_rpow_mul_of_tsupport
    (K : Type) [Field K] [NumberField K]
    (F : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F)
    (hFu : ∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport F, ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)])
    (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K =>
        ((((∏ w : NumberField.InfinitePlace K,
            ‖NumberField.AdelicLevel.archEval K w ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ ^ w.mult) ^ s
            : ℝ) : ℂ)) * F p) ∧
    HasCompactSupport (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K =>
        ((((∏ w : NumberField.InfinitePlace K,
            ‖NumberField.AdelicLevel.archEval K w ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ ^ w.mult) ^ s
            : ℝ) : ℂ)) * F p) ∧
    ∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
      ∀ p ∈ tsupport (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K =>
        ((((∏ w : NumberField.InfinitePlace K,
            ‖NumberField.AdelicLevel.archEval K w ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ ^ w.mult) ^ s
            : ℝ) : ℂ)) * F p), ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)] := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_contDiff_and_hasCompactSupport_prod_norm_archEval_pow_rpow_mul_of_tsupport.solution
