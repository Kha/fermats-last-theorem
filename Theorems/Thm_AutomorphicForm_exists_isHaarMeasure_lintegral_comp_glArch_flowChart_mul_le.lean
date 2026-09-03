import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped Classical

theorem AutomorphicForm.exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le
    (K : Type) [Field K] [NumberField K]
    (L₀ : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))
    (hL₀ : L₀.Nodup) (hL₀' : ∀ d, d ∈ L₀)
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))] :
    let flow : ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) → ℝ → AdelicGL2 (𝓞 K) K :=
      fun d t => Sum.elim (fun d => archFlowAt d.2.1 d.2.2 t) (fun d => archFlowAtComplex d.2.1 d.2.2 t) d
    let chart : (Fin L₀.length → ℝ) → AdelicGL2 (𝓞 K) K :=
      fun t => (List.ofFn fun j => flow (L₀.get j) (t j)).prod
    let scal : ({w : InfinitePlace K // w.IsReal} → ℝ) → ({w : InfinitePlace K // w.IsComplex} → ℂ) → AdelicGL2 (𝓞 K) K :=
      fun a b =>
        ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.map fun w =>
            archRealGLAt w.2 (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom
              (Units.mk0 (Real.exp (a w)) (Real.exp_ne_zero (a w))))).prod *
        ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.map fun w =>
            archComplexGLAt w.2 (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
              (Units.mk0 (Complex.exp (b w)) (Complex.exp_ne_zero (b w))))).prod
    ∃ μ : Measure (GL (Fin 2) (InfiniteAdeleRing K)), μ.IsHaarMeasure ∧ μ.Regular ∧
      ∃ ℓ : ℝ, 0 < ℓ ∧ ℓ ≤ 1 / 4 ∧ ∃ S : Set (GL (Fin 2) (InfiniteAdeleRing K)), IsCompact S ∧ ∃ c : NNReal,
        ∀ H : GL (Fin 2) (InfiniteAdeleRing K) → ENNReal, Measurable H →
          ∫⁻ v in (Set.pi Set.univ fun _ : Fin L₀.length => Set.Icc (-ℓ) ℓ) ×ˢ
              ((Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsReal} => Set.Icc (-ℓ) ℓ) ×ˢ
                (Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsComplex} => Metric.closedBall (0 : ℂ) ℓ)),
            H (glArch (𝓞 K) K (chart v.1 * scal v.2.1 v.2.2)) ≤
          (c : ENNReal) * ∫⁻ g in S, H g ∂μ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le.solution
