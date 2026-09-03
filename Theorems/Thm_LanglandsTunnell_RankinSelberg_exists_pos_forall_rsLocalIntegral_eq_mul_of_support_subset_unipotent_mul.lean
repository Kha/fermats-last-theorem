import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_eq_mul_of_support_subset_unipotent_mul

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
  LanglandsTunnell.TateLocal UnramifiedWhittaker

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_rsLocalIntegral_eq_mul_of_support_subset_unipotent_mul
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure]
      (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
      (_hUc : IsCompact (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
      (_hUo : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
      (_hUdet : ∀ u ∈ U,
        modulus ((Matrix.GeneralLinearGroup.det u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1),
    ∃ c : ℝ, 0 < c ∧
      ∀ (s : ℂ) (W F : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
          W (unipotent x * g) * F (unipotent x * g) = W g * F g) →
        (∀ g : GL (Fin 2) (p.adicCompletion ℚ), W g * F g ≠ 0 →
          ∃ (x : p.adicCompletion ℚ) (u : GL (Fin 2) (p.adicCompletion ℚ)), u ∈ U ∧ g = unipotent x * u) →
        (∀ u ∈ U, W u * F u = W 1 * F 1) →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
            s W F = (c : ℂ) * (W 1 * F 1) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_eq_mul_of_support_subset_unipotent_mul.solution
