import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime

set_option autoImplicit false

open scoped TensorProduct
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [Field A] [Algebra K A]
    (a b : Aˣ) (hab : a ≠ b) (α β : (L ⊗[K] A)ˣ)
    (hN : AutomorphicForm.normString K L A σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L A (diagUnits2 a b)) :
    AutomorphicForm.twistedCentralizer K L A σ (diagUnits2 α β) =
      (Subgroup.centralizer ({diagUnits2 a b} : Set (GL (Fin 2) A))).map (AutomorphicForm.toTensorGL K L A) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime.solution
