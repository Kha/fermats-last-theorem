import Definitions.Def_ModularCurve_ComponentGroup
import Theorems.Thm_ModularCurve_natCard_componentGroup_eq_kirchhoffCount
import Theorems.Thm_ModularCurve_componentGroup_subsingleton
import P2M.Util
namespace P2MW.S_ModularCurve_finite_componentGroup_of_pos

set_option autoImplicit false

open ModularCurve in
theorem solution {ι : Type*} [Fintype ι] (e : ι → ℕ)
    (he : ∀ x, 0 < e x) : Finite (componentGroup e) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI : Subsingleton (componentGroup e) :=
      componentGroup_subsingleton ((Fintype.card_eq_zero (α := ι)).le.trans zero_le_one) e
    infer_instance
  · have hcard : Nat.card (componentGroup e) = kirchhoffCount e :=
      natCard_componentGroup_eq_kirchhoffCount he
    exact Nat.finite_of_card_ne_zero (by rw [hcard]; exact (kirchhoffCount_pos he).ne')
