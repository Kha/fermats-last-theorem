import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isHaarMeasure_and_isOrbitalIntegralOn_centralScalar_smul_adelicGLHaar

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem AutomorphicForm.exists_isHaarMeasure_and_isOrbitalIntegralOn_centralScalar_smul_adelicGLHaar
    (K : Type) [Field K] [NumberField K]
    (c₀ : NNReal) (u : (AdeleRing (𝓞 K) K)ˣ) (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) :
    ∃ τ : Measure (Subgroup.centralizer
        ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
      τ.IsHaarMeasure ∧
      AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
        (AutomorphicForm.centralScalar (𝓞 K) K u) τ f
        (((c₀ : ℝ) : ℂ) * f (AutomorphicForm.centralScalar (𝓞 K) K u)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isHaarMeasure_and_isOrbitalIntegralOn_centralScalar_smul_adelicGLHaar.solution
