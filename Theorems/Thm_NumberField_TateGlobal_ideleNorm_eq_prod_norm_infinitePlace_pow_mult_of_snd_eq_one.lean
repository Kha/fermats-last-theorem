import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
    (K : Type) [Field K] [NumberField K]
    (a : (AdeleRing (𝓞 K) K)ˣ) (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) :
    NumberField.TateGlobal.ideleNorm K a = ∏ w : InfinitePlace K, ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ w.mult := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one.solution
