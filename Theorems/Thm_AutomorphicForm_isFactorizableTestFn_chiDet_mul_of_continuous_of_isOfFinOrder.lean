import Mathlib
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder

set_option autoImplicit false

open NumberField IsDedekindDomain
open AutomorphicForm

theorem AutomorphicForm.isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder
    (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hηc : Continuous η) (hηo : IsOfFinOrder η)
    (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hf : IsFactorizableTestFn F f) :
    IsFactorizableTestFn F (fun g => chiDet (𝓞 F) F η g * f g) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder.solution
