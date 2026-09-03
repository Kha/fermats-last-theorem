import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
namespace P2MW.S_padicPlace_liesOverPrime

set_option autoImplicit false

theorem solution (p : ℕ) [Fact p.Prime] :
    (padicPlace p).LiesOverPrime p := by
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hnorm : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p]
  change (p : AlgebraicClosure ℚ) ∈ (padicPlace p).nonunits
  rw [ValuationSubring.mem_nonunits_iff, Valuation.val_lt_one_iff _ hp0, ← not_le,
    ValuationSubring.valuation_le_one_iff, mem_padicPlace_iff, map_inv₀, map_natCast, nnnorm_inv,
    not_le, ← NNReal.coe_lt_coe, NNReal.coe_inv, coe_nnnorm, hnorm, inv_inv, NNReal.coe_one]
  exact_mod_cast (Fact.out : p.Prime).one_lt
