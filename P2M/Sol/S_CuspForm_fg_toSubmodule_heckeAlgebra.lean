import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import P2M.Util
namespace P2MW.S_CuspForm_fg_toSubmodule_heckeAlgebra
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

theorem solution (N : ℕ) [NeZero N] (S : Set ℕ) :
    (Subalgebra.toSubmodule (CuspForm.heckeAlgebra N 2 S)).FG :=
  Module.Finite.iff_fg.mp (CuspForm.moduleFinite_heckeAlgebra_two N S)
