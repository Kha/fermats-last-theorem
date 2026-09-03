import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_KummerTheory_powerSubgroup_eq_closure_sup_range_of_isSplittingField

set_option autoImplicit false
theorem KummerTheory.powerSubgroup_eq_closure_sup_range_of_isSplittingField (K L : Type) [Field K] [Field L]
    [Algebra K L] {n : ℕ} (hμ : (primitiveRoots n K).Nonempty) (S : Finset Kˣ)
    [Polynomial.IsSplittingField K L (∏ u ∈ S, (Polynomial.X ^ n - Polynomial.C ((u : Kˣ) : K)))] :
    groupCohomology.Kummer.powerSubgroup K L n
      = Subgroup.closure (S : Set Kˣ) ⊔ (powMonoidHom n : Kˣ →* Kˣ).range := by p2m_exact_reverting @_root_.P2MW.S_KummerTheory_powerSubgroup_eq_closure_sup_range_of_isSplittingField.solution
