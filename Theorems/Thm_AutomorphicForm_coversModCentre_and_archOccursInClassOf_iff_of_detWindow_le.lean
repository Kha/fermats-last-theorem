import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import P2M.Util
import P2M.Sol.S_AutomorphicForm_coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ dp : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hdp : 0 < dp) (hdp₂ : dp < d₂) (hd₁ : d₁ ≤ dp)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True)) :
    CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u dp d₂) ∧
    ∀ P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ P ↔
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u dp d₂) Θ P := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le.solution
