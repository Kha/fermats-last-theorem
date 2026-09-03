import Definitions.Def_AutomorphicForm_UnipotentQuotient
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integral_unipotentQuotient_out_mul_of_central

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.integral_unipotentQuotient_out_mul_of_central
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : AdelicGL2 (𝓞 ℚ) ℚ) (hz : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, z * g = g * z)
    (f : AdelicGL2 (𝓞 ℚ) ℚ → E)
    (hf : ∀ (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), f ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) = f g) :
    (∫ q, f (Quotient.out q * z) ∂(unipotentQuotientMeasure ℚ) =
        ∫ q, f (Quotient.out q) ∂(unipotentQuotientMeasure ℚ)) ∧
    (Integrable (fun q : UnipotentQuotient ℚ => f (Quotient.out q * z)) (unipotentQuotientMeasure ℚ) ↔
      Integrable (fun q : UnipotentQuotient ℚ => f (Quotient.out q)) (unipotentQuotientMeasure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integral_unipotentQuotient_out_mul_of_central.solution
