import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
namespace P2MW.S_PadicAlgCl_mem_range_algebraMap_of_forall_algEquiv_ringOfIntegers_apply_eq

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (K' : Type) [Field K'] [Algebra (PadicAlgCl.ringOfIntegers p K) K']
    [IsFractionRing (PadicAlgCl.ringOfIntegers p K) K']
    [Algebra K' (PadicAlgCl p)] [IsScalarTower (PadicAlgCl.ringOfIntegers p K) K' (PadicAlgCl p)]
    (x : PadicAlgCl p)
    (hx : ∀ τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p, τ x = x) :
    x ∈ Set.range (algebraMap K' (PadicAlgCl p)) := by

  have hxK : x ∈ K := by
    have hfix : x ∈ IntermediateField.fixedField K.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      exact hx (PadicAlgCl.ringOfIntegers.algEquivOfMemFixingSubgroup p K σ hσ)
    rwa [InfiniteGalois.fixedField_fixingSubgroup] at hfix

  obtain ⟨m, y, hy⟩ := PadicAlgCl.ringOfIntegers.exists_pow_natCast_mul_mem p K hxK
  have hp0 : ((p : PadicAlgCl p) ^ m) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hOy : algebraMap K' (PadicAlgCl p) (algebraMap (PadicAlgCl.ringOfIntegers p K) K' y) =
      (y : PadicAlgCl p) :=
    (IsScalarTower.algebraMap_apply (PadicAlgCl.ringOfIntegers p K) K' (PadicAlgCl p) y).symm
  have hOp : algebraMap K' (PadicAlgCl p)
      (algebraMap (PadicAlgCl.ringOfIntegers p K) K' (((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ^ m)) =
      (p : PadicAlgCl p) ^ m := by
    rw [← IsScalarTower.algebraMap_apply (PadicAlgCl.ringOfIntegers p K) K' (PadicAlgCl p), map_pow,
      map_natCast]
  refine ⟨algebraMap (PadicAlgCl.ringOfIntegers p K) K' y /
      algebraMap (PadicAlgCl.ringOfIntegers p K) K' (((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ^ m), ?_⟩
  rw [map_div₀, hOy, hOp, hy, mul_div_assoc, mul_div_cancel₀ _ hp0]
