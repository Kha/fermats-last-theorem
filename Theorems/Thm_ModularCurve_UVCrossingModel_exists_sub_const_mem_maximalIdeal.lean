import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_sub_const_mem_maximalIdeal

set_option autoImplicit false

p2m_open "ModularCurve ModularCurve.UVCrossingModel~maximalIdeal_eq_map_maximalIdeal_sup_span_pair"

theorem ModularCurve.UVCrossingModel.exists_sub_const_mem_maximalIdeal
    {W : Type*} [CommRing W] [IsLocalRing W] {π : W} (hπu : ¬IsUnit π) [IsLocalRing (UVCrossingModel W π)]
    (x : UVCrossingModel W π) :
    ∃ w : W, x - const π w ∈ IsLocalRing.maximalIdeal (UVCrossingModel W π) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_sub_const_mem_maximalIdeal.solution
