import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_continuous_hasCompactSupport_isSemiLocalFactorization_and_union_of_isArchTestFactor_of_isSemiLocalTestFn

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm
open scoped TensorProduct

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_continuous_hasCompactSupport_isSemiLocalFactorization_and_union_of_isArchTestFactor_of_isSemiLocalTestFn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : IsArchTestFactor L φa)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφS : ∀ v ∈ S, IsSemiLocalTestFn K L v (φS v)) :
    ∃ (φ₀ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (φf₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      Continuous φ₀ ∧ HasCompactSupport φ₀ ∧ IsSemiLocalFactorization K L S φ₀ φa φf₀ φS ∧
      ∀ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint T S →
        IsSemiLocalFactorization K L (S ∪ T) φ₀ φa φf₀
          (fun v => if v ∈ T then (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) else φS v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_continuous_hasCompactSupport_isSemiLocalFactorization_and_union_of_isArchTestFactor_of_isSemiLocalTestFn.solution
