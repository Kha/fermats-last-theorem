import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen

set_option autoImplicit false

open NumberField AutomorphicForm MeasureTheory IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped Classical in

theorem AutomorphicForm.exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen
    (K : Type) [Field K] [NumberField K]
    (U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    (hU'c : IsCompact (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))))
    (hU'o : IsOpen (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ, Continuous Φ → HasCompactSupport Φ →
        tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} →
          ∫ x, Φ (archEntries K (AdelicLevel.glArch (𝓞 K) K x)) *
              (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ))
                (AdelicLevel.glFin (𝓞 K) K x) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) =
            c * ∫ E, Φ E * (((mixedEmbedding.norm (Matrix.det (Matrix.of E)))⁻¹ ^ 2 : ℝ) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen.solution
