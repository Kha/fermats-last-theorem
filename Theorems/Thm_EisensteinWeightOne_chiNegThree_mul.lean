import Mathlib
import Definitions.Def_ModularForm_EisensteinChiNegThree
import P2M.Util
import P2M.Sol.S_EisensteinWeightOne_chiNegThree_mul

open EisensteinWeightOne
theorem EisensteinWeightOne.chiNegThree_mul (m n : ℕ) :
  EisensteinWeightOne.chiNegThree (m * n) =
    EisensteinWeightOne.chiNegThree m * EisensteinWeightOne.chiNegThree n := by p2m_exact_reverting @_root_.P2MW.S_EisensteinWeightOne_chiNegThree_mul.solution
