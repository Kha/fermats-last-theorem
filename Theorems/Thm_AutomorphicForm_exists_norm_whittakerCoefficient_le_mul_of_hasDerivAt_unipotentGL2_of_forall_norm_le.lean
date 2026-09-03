import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

theorem AutomorphicForm.exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (M : ℕ) (v : mixedEmbedding.mixedSpace K)
    (hv : ∃ t : ℝ, NumberField.StandardAddChar.stdAddChar K
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0) ≠ 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (xs : ℕ → AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) (A : ℝ),
        (∀ j : ℕ, Continuous (xs j)) →
        (∀ (j : ℕ) (β : K) (h : AdelicGL2 (𝓞 K) K),
          xs j (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) = xs j h) →
        (∀ (j : ℕ) (u : AdeleRing (𝓞 K) K),
          HasDerivAt (fun t : ℝ => xs j (unipotentGL2 (R := AdeleRing (𝓞 K) K)
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0) * (unipotentGL2 u * g)))
            (xs (j + 1) (unipotentGL2 u * g)) 0) →
        (∀ u : AdeleRing (𝓞 K) K, ‖xs M (unipotentGL2 u * g)‖ ≤ A) →
        ‖whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) (xs 0) 1 g‖ ≤ c * A := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le.solution
