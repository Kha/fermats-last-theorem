import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2

set_option autoImplicit false

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct in

theorem AutomorphicForm.exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (A : Type) [CommRing A] [Algebra K A]
    (a b : Aˣ) (hab : IsUnit ((a : A) - (b : A)))
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.normString K L A σ δ = AutomorphicForm.toTensorGL K L A (diagUnits2 a b)) :
    ∃ α β : (L ⊗[K] A)ˣ, δ = diagUnits2 α β := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2.solution
