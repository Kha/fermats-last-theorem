module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import Theorems.Thm_WeierstrassCurve_hasseInvariant_variableChange
import P2M.Util

@[expose] public section
namespace P2MW.S_WeierstrassCurve_hasseInvariant_pow_mul_delta_pow_eq_of_j_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open WeierstrassCurve

namespace P2mWs11W0

theorem hasseInvariant_pow_mul_Δ_pow_variableChange (q : ℕ) [Fact q.Prime]
    {R : Type*} [CommRing R] [CharP R q] (W : WeierstrassCurve R) (φ : VariableChange R) :
    hasseInvariant q (φ • W) ^ 12 * W.Δ ^ (q - 1) = hasseInvariant q W ^ 12 * (φ • W).Δ ^ (q - 1) := by
  rw [hasseInvariant_variableChange W φ, variableChange_Δ, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
    mul_comm 12 (q - 1)]
  ring

end P2mWs11W0

open ModularCurve in
theorem solution
    (q : ℕ) [Fact q.Prime]
    {F : Type*} [Field F] [CharP F q] [IsSepClosed F]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic] (h : W.j = W'.j) :
    WeierstrassCurve.hasseInvariant q W ^ 12 * W'.Δ ^ (q - 1) =
      WeierstrassCurve.hasseInvariant q W' ^ 12 * W.Δ ^ (q - 1) := by
  obtain ⟨φ, rfl⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W W' h
  exact (P2mWs11W0.hasseInvariant_pow_mul_Δ_pow_variableChange q W φ).symm
