import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
import P2M.Sol.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_mul_unipotent_eq

set_option autoImplicit false

theorem AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_mul_unipotent_eq
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hpsi : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (AutomorphicForm.unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
    (hsm : ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
    (hfix : ∀ x : p.adicCompletion ℚ, (fun g => W (g * AutomorphicForm.unipotentGL2 x)) = W) :
    W = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_mul_unipotent_eq.solution
