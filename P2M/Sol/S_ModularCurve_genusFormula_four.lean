import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
namespace P2MW.S_ModularCurve_genusFormula_four

set_option autoImplicit false

namespace Ws23
namespace GenusNumerics4
open ModularCurve

theorem divisors_eq : Nat.divisors 4 = {1, 2, 4} := by decide

theorem dedekindPsi_eq : dedekindPsi 4 = 6 := by
  rw [dedekindPsi, divisors_eq]
  have h1 : Squarefree (1 : ℕ) := squarefree_one
  have h2 : Squarefree (2 : ℕ) := Nat.prime_two.prime.squarefree
  have h4 : ¬ Squarefree (4 : ℕ) := fun h => by
    have := h 2 ⟨1, by norm_num⟩
    rw [Nat.isUnit_iff] at this; omega
  rw [Finset.filter_insert, if_pos h1, Finset.filter_insert, if_pos h2, Finset.filter_singleton, if_neg h4]
  decide

theorem cuspCount_eq : cuspCount 4 = 3 := by decide

theorem nuTwo_eq : nuTwo 4 = 0 := by
  rw [nuTwo, Nat.card_eq_fintype_card]; decide

theorem nuThree_eq : nuThree 4 = 0 := by
  rw [nuThree, Nat.card_eq_fintype_card]; decide

theorem main : genusFormula 4 = 0 := by
  rw [genusFormula, dedekindPsi_eq, cuspCount_eq, nuTwo_eq, nuThree_eq]
  norm_num

end Ws23.GenusNumerics4

theorem solution : ModularCurve.genusFormula 4 = 0 :=
  Ws23.GenusNumerics4.main
