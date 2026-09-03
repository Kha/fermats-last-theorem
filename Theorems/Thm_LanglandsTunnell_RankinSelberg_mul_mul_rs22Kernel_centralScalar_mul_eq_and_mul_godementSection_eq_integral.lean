import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Mathlib.MeasureTheory.Group.FundamentalDomain
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_mul_mul_rs22Kernel_centralScalar_mul_eq_and_mul_godementSection_eq_integral

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicFourier IsDedekindDomain NumberField.TateGlobal
open AutomorphicForm LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.mul_mul_rs22Kernel_centralScalar_mul_eq_and_mul_godementSection_eq_integral
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ)
    (μ ν ω ω' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hωμν : ω * ω' * μ * ν = 1)
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ)
    (W W' : AdelicGL2 (𝓞 F) F → ℂ)
    (hZ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      W (centralScalar (𝓞 F) F z * g) * W' (centralScalar (𝓞 F) F z * g) =
        ((ω z : ℂˣ) : ℂ) * ((ω' z : ℂˣ) : ℂ) * (W g * W' g))
    (g : AdelicGL2 (𝓞 F) F) :
    (∀ t : (AdeleRing (𝓞 F) F)ˣ,
      W (centralScalar (𝓞 F) F t * g) * W' (centralScalar (𝓞 F) F t * g) *
          rs22Kernel F μ (moduleChar F) (moduleChar_pos F) Φ s (centralScalar (𝓞 F) F t * g) =
        W g * W' g *
          (((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((cpowChar (moduleChar F) (moduleChar_pos F) (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) *
          (Φ (bottomRowVec F g t) * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1))) ∧
    W g * W' g * godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s g =
      ∫ t : (AdeleRing (𝓞 F) F)ˣ,
        W (centralScalar (𝓞 F) F t * g) * W' (centralScalar (𝓞 F) F t * g) *
          rs22Kernel F μ (moduleChar F) (moduleChar_pos F) Φ s (centralScalar (𝓞 F) F t * g) ∂ν₀ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_mul_mul_rs22Kernel_centralScalar_mul_eq_and_mul_godementSection_eq_integral.solution
