import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_isCompact_bigCell_inter_support_subset_finUnipotent_mul

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel

open MeasureTheory NumberField AutomorphicForm IsDedekindDomain UnramifiedWhittaker
open LanglandsTunnell.RankinSelberg

open scoped Pointwise

theorem LanglandsTunnell.RankinSelberg.exists_isCompact_bigCell_inter_support_subset_finUnipotent_mul
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hsupp : ∃ (Cpt : Set (finiteAdelicGL2Subgroup ℚ)) (B₀ : ℝ), IsCompact Cpt ∧
      (∀ g : finiteAdelicGL2Subgroup ℚ, ‖W g * F g‖ ≤ B₀) ∧
      ∀ g : finiteAdelicGL2Subgroup ℚ,
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
          ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
            ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
        W g * F g ≠ 0 →
          ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
            ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
              localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)) :
    ∃ K' : Set (finiteAdelicGL2Subgroup ℚ), IsCompact K' ∧
      {g : finiteAdelicGL2Subgroup ℚ |
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k) ∧ W g * F g ≠ 0} ⊆
        ((RSCarrier.finUnipotent : Subgroup (finiteAdelicGL2Subgroup ℚ)) : Set (finiteAdelicGL2Subgroup ℚ)) * K' := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_isCompact_bigCell_inter_support_subset_finUnipotent_mul.solution
