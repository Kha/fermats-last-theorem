import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm hiding hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (j : ℕ)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), ψ (globalPoints (𝓞 K) K γ * g) = ψ g) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    (∀ l, l.length ≤ j →
      Continuous (W l ψ) ∧
      (∀ (v : InfinitePlace K) (hv : v.IsReal), IsArchSmoothAt hv (W l ψ)) ∧
      (∀ (v : InfinitePlace K) (hv : v.IsComplex), IsArchSmoothAtComplex hv (W l ψ)) ∧
      ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β → ‖W l ψ g‖ ≤ B) →
    ∀ (w : InfinitePlace K) (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion),
      (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        rightTranslate K (rowIsometryInclAt₀ K w k) ψ (globalPoints (𝓞 K) K γ * g) =
          rightTranslate K (rowIsometryInclAt₀ K w k) ψ g) ∧
      ∀ l, l.length ≤ j →
        Continuous (W l (rightTranslate K (rowIsometryInclAt₀ K w k) ψ)) ∧
        (∀ (v : InfinitePlace K) (hv : v.IsReal), IsArchSmoothAt hv (W l (rightTranslate K (rowIsometryInclAt₀ K w k) ψ))) ∧
        (∀ (v : InfinitePlace K) (hv : v.IsComplex),
          IsArchSmoothAtComplex hv (W l (rightTranslate K (rowIsometryInclAt₀ K w k) ψ))) ∧
        ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β →
            ‖W l (rightTranslate K (rowIsometryInclAt₀ K w k) ψ) g‖ ≤ B := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt.solution
