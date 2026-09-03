import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isArithBoundedGenuineCuspRealizable_of_isArithBoundedGenuineCuspRealizable_of_pos_of_pos

open NumberField AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.isArithBoundedGenuineCuspRealizable_of_isArithBoundedGenuineCuspRealizable_of_pos_of_pos
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K) (B : Set (AdeleRing (𝓞 K) K))
    (Φ : HeckeEigensystem K ℂ)
    (hΦ : IsArithBoundedGenuineCuspRealizable K (productionPinsOf K D U gen B)
      (StandardAddChar.stdAddChar K) Φ)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁) :
    IsArithBoundedGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B)
      (StandardAddChar.stdAddChar K) Φ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isArithBoundedGenuineCuspRealizable_of_isArithBoundedGenuineCuspRealizable_of_pos_of_pos.solution
