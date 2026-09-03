import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal NumberField.AdelicLevel

theorem AutomorphicForm.WhittakerModel.exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible
    (p : HeightOneSpectrum (𝓞 ℚ))
    (V : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ V)
    (hsm : ∀ W ∈ V, ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)
    (hadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ V, (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
        W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hirr : ∀ W₀ ∈ V, W₀ ≠ 0 → ∀ W ∈ V,
      W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) :
    ∃ S : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), (↑S : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)) ⊆ V ∧
      ∀ W ∈ V, ∃ c : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) → ℂ,
        (W - ∑ s ∈ S, c s • s) ∈ Submodule.span ℂ {f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ W' ∈ V, ∃ t : p.adicCompletion ℚ, f = fun g => W' (g * unipotent t) - W' g} := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible.solution
