import Mathlib
import Definitions.Def_DualSelmer_ExtConditions
import P2M.Util
namespace P2MW.S_groupCohomology_isMulCocycle1_pow_val_iff_mem_cocycles1_ofChar

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology
open scoped IntermediateField Pointwise

private theorem twist_trivial_apply_apply_b {k : Type u} [Field k] {Γ : Type u} [Group Γ]
    (ψ : Γ →* kˣ) (g : Γ) (x : k) : (Representation.trivial k Γ k).twist ψ g x = (ψ g : k) * x := rfl

theorem solution
    {K L : Type} [Field K] [Field L] [Algebra K L] {p : ℕ} [Fact p.Prime]
    (χ : (L ≃ₐ[K] L) →* (ZMod p)ˣ) {ζ : Lˣ} (hζp : IsPrimitiveRoot ζ p)
    (hζ : ∀ g : L ≃ₐ[K] L, g • ζ = ζ ^ (χ g : ZMod p).val) (c : (L ≃ₐ[K] L) → ZMod p) :
    IsMulCocycle₁ (fun g => ζ ^ (c g).val) ↔ c ∈ cocycles₁ (ofChar χ) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have key : ∀ g h : L ≃ₐ[K] L,
      (ζ ^ (c (g * h)).val = g • ζ ^ (c h).val * ζ ^ (c g).val ↔
        c (g * h) = (χ g : ZMod p) * c h + c g) := by
    intro g h
    rw [smul_pow', hζ, ← pow_mul, ← pow_add, pow_eq_pow_iff_modEq, ← hζp.eq_orderOf, ← ZMod.natCast_eq_natCast_iff]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  simp only [IsMulCocycle₁, mem_cocycles₁_iff, key, twist_trivial_apply_apply_b]
