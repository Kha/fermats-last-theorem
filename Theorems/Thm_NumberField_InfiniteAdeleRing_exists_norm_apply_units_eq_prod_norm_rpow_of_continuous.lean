import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_InfiniteAdeleRing_exists_norm_apply_units_eq_prod_norm_rpow_of_continuous

set_option autoImplicit false

open NumberField

theorem NumberField.InfiniteAdeleRing.exists_norm_apply_units_eq_prod_norm_rpow_of_continuous
    (K : Type) [Field K] [NumberField K]
    (χ : (InfiniteAdeleRing K)ˣ →* ℂˣ) (hχ : Continuous fun y : (InfiniteAdeleRing K)ˣ => ((χ y : ℂˣ) : ℂ)) :
    ∃ σ : InfinitePlace K → ℝ, ∀ y : (InfiniteAdeleRing K)ˣ,
      ‖((χ y : ℂˣ) : ℂ)‖ = ∏ w : InfinitePlace K, ‖(y : InfiniteAdeleRing K) w‖ ^ σ w := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfiniteAdeleRing_exists_norm_apply_units_eq_prod_norm_rpow_of_continuous.solution
