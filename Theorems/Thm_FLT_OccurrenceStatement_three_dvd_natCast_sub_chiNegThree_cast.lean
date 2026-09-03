import Mathlib
import Definitions.Def_ModularForm_EisensteinChiNegThree
import P2M.Util
import P2M.Sol.S_FLT_OccurrenceStatement_three_dvd_natCast_sub_chiNegThree_cast

open EisensteinWeightOne
theorem FLT.OccurrenceStatement.three_dvd_natCast_sub_chiNegThree_cast
    (R : Type*) [CommRing R] (ℓ : ℕ) :
    (3 : R) ∣ (ℓ : R) - ((chiNegThree ℓ : ℤ) : R) := by p2m_exact_reverting @_root_.P2MW.S_FLT_OccurrenceStatement_three_dvd_natCast_sub_chiNegThree_cast.solution
