import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpand_mem_xHFunctionField_of_mem_div

set_option autoImplicit false

p2m_open "ModularCurve~qExpand_image_intFormRatiosC_subset~exists_conj_mem_GammaH_div"
open scoped MatrixGroups

theorem ModularCurve.qExpand_mem_xHFunctionField_of_mem_div
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    {y : LaurentSeries ℚ} (hy : y ∈ xHFunctionField (M / p) (infSubgroup p M H hpM)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    qExpand ℚ p y ∈ xHFunctionField M H := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpand_mem_xHFunctionField_of_mem_div.solution
