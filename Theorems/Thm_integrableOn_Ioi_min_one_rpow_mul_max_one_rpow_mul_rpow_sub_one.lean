import Mathlib
import P2M.Util
import P2M.Sol.S_integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one

set_option autoImplicit false

open MeasureTheory

theorem integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one
    (p q c : ℝ) (hpc : 0 < p + c) (hcq : c < q) :
    IntegrableOn (fun r : ℝ => (min 1 r) ^ p * (max 1 r) ^ (-q) * r ^ (c - 1)) (Set.Ioi 0) := by p2m_exact_reverting @_root_.P2MW.S_integrableOn_Ioi_min_one_rpow_mul_max_one_rpow_mul_rpow_sub_one.solution
