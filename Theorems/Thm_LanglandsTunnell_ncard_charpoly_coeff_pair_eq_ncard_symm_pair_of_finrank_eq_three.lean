import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Data.Set.Card
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ncard_charpoly_coeff_pair_eq_ncard_symm_pair_of_finrank_eq_three

set_option autoImplicit false

theorem LanglandsTunnell.ncard_charpoly_coeff_pair_eq_ncard_symm_pair_of_finrank_eq_three
    (F : Type) [Field F] [Fintype F] (F' : Type) [Field F'] [Algebra F F'] [Fintype F']
    (h3 : Module.finrank F F' = 3) (t s : F) :
    {y : F' | -(LinearMap.charpoly (Algebra.lmul F F' y)).coeff 2 = t ∧
        (LinearMap.charpoly (Algebra.lmul F F' y)).coeff 1 = s}.ncard
      = {r : F × F × F | r.1 + r.2.1 + r.2.2 = t ∧ r.1 * r.2.1 + r.2.1 * r.2.2 + r.2.2 * r.1 = s}.ncard := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ncard_charpoly_coeff_pair_eq_ncard_symm_pair_of_finrank_eq_three.solution
