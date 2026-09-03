import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin 2) (v.adicCompletion F))
    (_hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (_hg' : ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
      ∈ v.adicCompletionIntegers F) :
    ∃ (β : GL (Fin 2) (v.adicCompletion F)) (x : v.adicCompletion F),
      (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 ∧
      (∀ i j, (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F) ∧
      (∀ i j, ((β⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
        ∈ v.adicCompletionIntegers F) ∧
      x ∈ v.adicCompletionIntegers F ∧
      (g = β * gl2Weyl * unipotentGL2 x ∨ g = β * gl2Weyl * unipotentGL2 x * gl2Weyl⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral.solution
