import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_rsEulerPoly_induced_eq_finprod_twist_formalBaseChange

set_option autoImplicit false
open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.rsEulerPoly_induced_eq_finprod_twist_formalBaseChange
    (K : Type) [Field K] [NumberField K]
    [Algebra (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)]
    [Algebra.IsIntegral (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)]
    (hdeg : Module.finrank ℚ K = 3)
    (Pi : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (μ : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ →* ℂˣ)
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    LanglandsTunnell.RankinSelberg.rsEulerPoly (Pi.a p) (Pi.b p)
        (LanglandsTunnell.RankinSelberg.inducedE1 ℚ
        (fun 𝔓 => if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p)
        (LanglandsTunnell.RankinSelberg.inducedE2 ℚ
        (fun 𝔓 => if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p)
        (LanglandsTunnell.RankinSelberg.inducedE3 ℚ
        (fun 𝔓 => if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p) =
      ∏ᶠ 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
        (if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then Polynomial.C 1
            - Polynomial.C (((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ)
                * (AutomorphicForm.formalBaseChange ℚ K Pi).a 𝔓)
              * Polynomial.X ^
                ((𝔓.under (NumberField.RingOfIntegers ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal)
            + Polynomial.C ((((μ (AutomorphicForm.uniformizerIdele K 𝔓))^2 : ℂˣ) : ℂ)
                * (AutomorphicForm.formalBaseChange ℚ K Pi).b 𝔓)
              * Polynomial.X ^
                (2 * ((𝔓.under (NumberField.RingOfIntegers ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
          else Polynomial.C 1) ∧
    LanglandsTunnell.RankinSelberg.rsEulerPoly (Pi.a p / Pi.b p) (Pi.b p)⁻¹
        (LanglandsTunnell.RankinSelberg.inducedE1 ℚ
        (fun 𝔓 => (if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹) p)
        (LanglandsTunnell.RankinSelberg.inducedE2 ℚ
        (fun 𝔓 => (if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹) p)
        (LanglandsTunnell.RankinSelberg.inducedE3 ℚ
        (fun 𝔓 => (if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (AutomorphicForm.uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹) p) =
      ∏ᶠ 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
        (if NumberField.TateGlobal.IsUnramifiedCharAt μ 𝔓
          then Polynomial.C 1
            - Polynomial.C ((((μ (AutomorphicForm.uniformizerIdele K 𝔓))⁻¹ : ℂˣ) : ℂ)
                * ((AutomorphicForm.formalBaseChange ℚ K Pi).a 𝔓
                    / (AutomorphicForm.formalBaseChange ℚ K Pi).b 𝔓))
              * Polynomial.X ^
                ((𝔓.under (NumberField.RingOfIntegers ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal)
            + Polynomial.C ((((μ (AutomorphicForm.uniformizerIdele K 𝔓))^(-2 : ℤ) : ℂˣ) : ℂ)
                * ((AutomorphicForm.formalBaseChange ℚ K Pi).b 𝔓)⁻¹)
              * Polynomial.X ^
                (2 * ((𝔓.under (NumberField.RingOfIntegers ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
          else Polynomial.C 1) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_rsEulerPoly_induced_eq_finprod_twist_formalBaseChange.solution
