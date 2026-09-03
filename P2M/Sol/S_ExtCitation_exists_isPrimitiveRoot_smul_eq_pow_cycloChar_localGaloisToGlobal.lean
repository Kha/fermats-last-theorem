import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
namespace P2MW.S_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal

set_option autoImplicit false
open ExtCitation
open scoped IntermediateField Pointwise

theorem solution
    (q : ℕ) [Fact q.Prime] (p : ℕ) [Fact p.Prime] :
    ∃ ζ : (PadicAlgCl q)ˣ, IsPrimitiveRoot ζ p ∧ ∀ g : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      g • ζ = ζ ^ (cycloChar p (localGaloisToGlobal q g) : ZMod p).val := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero p := ⟨hp0⟩
  haveI : NeZero (p : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hp0⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have hξu : IsUnit ξ := hξ.isUnit hp0
  have hιξ : IsPrimitiveRoot (padicEmbedding q ξ) p :=
    hξ.map_of_injective (padicEmbedding q : AlgebraicClosure ℚ →+* PadicAlgCl q).injective
  have hιξu : IsUnit (padicEmbedding q ξ) := hιξ.isUnit hp0
  refine ⟨hιξu.unit, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hιξ), fun g => ?_⟩
  ext

  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  change g (padicEmbedding q ξ) = _
  rw [← padicEmbedding_localGaloisToGlobal, ← map_pow]
  congr 1

  have hmem : hξu.unit ∈ rootsOfUnity p (AlgebraicClosure ℚ) := by
    rw [mem_rootsOfUnity]; ext; rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hξ.pow_eq_one, Units.val_one]
  have := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
    (localGaloisToGlobal q g : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) hmem
  simp [IsUnit.unit_spec] at this
  exact this
