import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one
import Theorems.Thm_ValuationSubring_isAlgClosed_completion_of_mulArchimedean_valueGroup
import P2M.Util
namespace P2MW.S_ValuationSubring_isAlgClosed_completion_of_liesOverPrime

theorem solution
    (p : ℕ) (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    IsAlgClosed A.valuation.Completion := by
  have hAp : A.valuation (p : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ
    rfl
    rfl
  haveI : MulArchimedean A.ValueGroup :=
    ValuationSubring.mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one A hp hAp
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hAtop : A ≠ ⊤ := by
    intro htop
    have hmem : (p : AlgebraicClosure ℚ)⁻¹ ∈ A := by rw [htop]; exact ValuationSubring.mem_top _
    have hle : A.valuation (p : AlgebraicClosure ℚ)⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr hmem
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((map_ne_zero A.valuation).mpr hp0))] at hle
    exact absurd hAp (not_lt.mpr hle)
  exact ValuationSubring.isAlgClosed_completion_of_mulArchimedean_valueGroup A hAtop
