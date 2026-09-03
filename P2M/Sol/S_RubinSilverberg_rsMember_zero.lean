import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
namespace P2MW.S_RubinSilverberg_rsMember_zero

open RubinSilverberg

theorem solution {K : Type*} [Field K] (a b u₀ l : K) (hH : kleinH u₀ ≠ 0) (hT : kleinT u₀ ≠ 0) : rsMember a b u₀ l 0 = ⟨0, 0, 0, a, b⟩ := by
  have hA : kleinHHom u₀ 1 = kleinH u₀ := by unfold kleinHHom kleinH; ring
  have hB : kleinTHom u₀ 1 = kleinT u₀ := by unfold kleinTHom kleinT; ring
  simp only [rsMember, rsFamilyA, rsFamilyB, rsNum, rsDen, mul_zero, zero_add, hA, hB,
    mul_div_assoc, div_self hH, div_self hT, mul_one]
