import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import P2M.Util
import P2M.Sol.S_AutomorphicForm_memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre

open NumberField NumberField.AdelicHaar MeasureTheory AutomorphicForm
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ₀ : AdelicGL2 (𝓞 F) F → ℂ) (hφ₀ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ₀) (hφ₀c : Continuous φ₀)
    (hφ₀ne : ∃ g, φ₀ g ≠ 0)
    (hφ₀L2 : @MemLp _ _ (glBorel (Fin 2) (𝓞 F) F) _ _ φ₀ 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)))
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : IsLsXiFunction (𝓞 F) F ⊤ ξ ψ) (hψc : Continuous ψ)
    (hψb : IsBoundedOnSiegelWindows F ψ) :
    @MemLp _ _ (glBorel (Fin 2) (𝓞 F) F) _ _ ψ 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre.solution
