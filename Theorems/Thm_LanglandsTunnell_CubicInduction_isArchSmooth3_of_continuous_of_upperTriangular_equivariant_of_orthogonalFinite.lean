import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isArchSmooth3_of_continuous_of_upperTriangular_equivariant_of_orthogonalFinite
attribute [-simp] LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
p2m_open "LanglandsTunnell.CubicInduction~archRealLift3_mul_eq_mul_archRealLift3_conj~componentAt3_archRealLift3_eq_one_and_realMat_archComponent3_eq"

theorem LanglandsTunnell.CubicInduction.isArchSmooth3_of_continuous_of_upperTriangular_equivariant_of_orthogonalFinite
    (ν : Fin 3 → ℂ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hcont : Continuous F)
    (heq : ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * F g)
    (hfin : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => F (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) :
    WhittakerBlock.IsArchSmooth3 F := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isArchSmooth3_of_continuous_of_upperTriangular_equivariant_of_orthogonalFinite.solution
