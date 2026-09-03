import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_dirichletIdeleChar_mul_modulus_det_gen
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField AutomorphicForm
open IsDedekindDomain

theorem LanglandsTunnell.dirichletIdeleChar_mul_modulus_det_gen
    {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℂ n)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ)
        = χ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_dirichletIdeleChar_mul_modulus_det_gen.solution
