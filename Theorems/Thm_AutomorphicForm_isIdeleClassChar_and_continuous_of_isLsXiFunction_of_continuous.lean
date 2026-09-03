import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous

open NumberField

theorem AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
    (K : Type) [Field K] [NumberField K]
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsLsXiFunction (𝓞 K) K ⊤ χ φ)
    (hcont : Continuous φ)
    (hne : ∃ g, φ g ≠ 0) :
    (∀ u : Kˣ, χ ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u, Subgroup.mem_top _⟩ = 1) ∧
      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => χ ⟨z, Subgroup.mem_top z⟩ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous.solution
