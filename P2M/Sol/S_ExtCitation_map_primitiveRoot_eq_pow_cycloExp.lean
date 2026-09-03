import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
namespace P2MW.S_ExtCitation_map_primitiveRoot_eq_pow_cycloExp

open ExtCitation
open ValuationSubring
variable {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
  [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]

theorem solution (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {ξ : AlgebraicClosure ℚ} (hξ : IsPrimitiveRoot ξ p) : σ ξ = ξ ^ cycloExp p σ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hspec := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ)
    (card_rootsOfUnity_eq_self p) (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)
    (SetLike.coe_mem hξ.toRootsOfUnity)
  rw [cycloExp]
  simpa [hξ.val_toRootsOfUnity_coe, Units.val_pow_eq_pow_val] using hspec
