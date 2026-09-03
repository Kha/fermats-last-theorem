import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import P2M.Util
import P2M.Sol.S_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel
  MeasureTheory

theorem AutomorphicForm.memLp_iUnion_centreCutSiegelSet_of_detWindow_le
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ dp : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hdp : 0 < dp) (hdp₂ : dp < d₂) (hd₁ : d₁ ≤ dp)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφm : letI := glBorel (Fin 2) (𝓞 F) F; AEStronglyMeasurable φ (adelicGLHaar (Fin 2) (𝓞 F) F))
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hω : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ g)
    (hcontr : d₁ ≤ 0 → ∀ (w : InfinitePlace F) (a : (w.Completion)ˣ), ‖(a : w.Completion)‖ < 1 →
      ‖((ω (AdelicVolume.archCentralUnit F w a) : ℂˣ) : ℂ)‖ < 1)
    (hL2 : letI := glBorel (Fin 2) (𝓞 F) F;
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u dp d₂))) :
    letI := glBorel (Fin 2) (𝓞 F) F;
    MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le.solution
