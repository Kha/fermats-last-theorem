import Definitions.Def_ModularCurve_ComponentGroupKirchhoff
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_natCard_componentGroup_eq_kirchhoffCount
import Theorems.Thm_ModularCurve_kirchhoffCount_eq_eisensteinNumerator_of_massFormula
import P2M.Util
namespace P2MW.S_ModularCurve_natCard_componentGroup_eq_eisensteinNumerator

open ModularCurve Finset

theorem solution {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (p : ℕ) (hp : 1 < p)
    (he : ∀ x, e x = 1 ∨ e x = 2 ∨ e x = 3)
    (h2 : ({x | e x = 2} : Set ι).Subsingleton)
    (h3 : ({x | e x = 3} : Set ι).Subsingleton)
    (hmass : ∑ x, ((e x : ℚ))⁻¹ = ((p : ℚ) - 1) / 12) :
    Nat.card (componentGroup e) = eisensteinNumerator p := by
  classical
  have hι : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hmass
    have : (p : ℚ) = 1 := by linarith
    exact absurd (by exact_mod_cast this : p = 1) (Nat.ne_of_gt hp)
  rw [natCard_componentGroup_eq_kirchhoffCount fun x => by rcases he x with h | h | h <;> omega]
  exact kirchhoffCount_eq_eisensteinNumerator_of_massFormula e p he h2 h3 hmass
