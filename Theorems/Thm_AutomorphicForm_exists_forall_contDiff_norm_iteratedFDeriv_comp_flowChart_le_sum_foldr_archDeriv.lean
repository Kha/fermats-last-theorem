import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv
    (K : Type) [Field K] [NumberField K]
    (L₀ : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))
    (ℓ : ℝ) (hℓ : 0 < ℓ) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    let flow : ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) → ℝ → AdelicGL2 (𝓞 K) K :=
      fun d t => Sum.elim (fun d => archFlowAt d.2.1 d.2.2 t) (fun d => archFlowAtComplex d.2.1 d.2.2 t) d
    let chart : (Fin L₀.length → ℝ) → AdelicGL2 (𝓞 K) K :=
      fun t => (List.ofFn fun j => flow (L₀.get j) (t j)).prod
    ∃ (Λ : Finset (List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))) (c : ℝ),
      (∀ l ∈ Λ, l.length ≤ L₀.length) ∧ 0 ≤ c ∧
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ,
        (∀ l, l.length ≤ L₀.length →
          Continuous (W l b) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l b)) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l b))) →
        ∀ x : AdelicGL2 (𝓞 K) K,
          ContDiff ℝ L₀.length (fun t : Fin L₀.length → ℝ => b (x * chart t)) ∧
          ∀ k : ℕ, k ≤ L₀.length → ∀ t : Fin L₀.length → ℝ, (∀ j, t j ∈ Set.Icc (-ℓ) ℓ) →
            ‖iteratedFDeriv ℝ k (fun t : Fin L₀.length → ℝ => b (x * chart t)) t‖ ≤
              c * ∑ l ∈ Λ, ‖W l b (x * chart t)‖ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv.solution
