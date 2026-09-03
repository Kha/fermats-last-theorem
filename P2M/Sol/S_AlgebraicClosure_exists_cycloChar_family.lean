import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicClosure_exists_cycloChar_family

set_option autoImplicit false

namespace CycQ

open Polynomial

local notation "ℚb" => AlgebraicClosure ℚ

theorem exists_isPrimitiveRoot (q : ℕ) [NeZero q] : ∃ μ : ℚb, IsPrimitiveRoot μ q := by
  have hdeg : (cyclotomic q ℚb).degree ≠ 0 := by
    rw [degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root (cyclotomic q ℚb) hdeg
  exact ⟨μ, (isRoot_cyclotomic_iff).mp hμ⟩

noncomputable def zeta (q : ℕ) [NeZero q] : ℚb := (exists_isPrimitiveRoot q).choose

theorem zeta_spec (q : ℕ) [NeZero q] : IsPrimitiveRoot (zeta q) q := (exists_isPrimitiveRoot q).choose_spec

noncomputable def cyc (q : ℕ) : (ℚb ≃ₐ[ℚ] ℚb) →* (ZMod q)ˣ :=
  if h : q = 0 then 1 else
    haveI : NeZero q := ⟨h⟩
    (zeta_spec q).autToPow ℚ

theorem cyc_of_ne_zero (q : ℕ) [hq : NeZero q] : cyc q = (zeta_spec q).autToPow ℚ := by
  unfold cyc
  rw [dif_neg (NeZero.ne q)]

theorem main :
    ∃ cyc : (q : ℕ) → ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ),
      ∀ q : ℕ, q.Prime → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
        μ ^ q = 1 → σ μ = μ ^ ((cyc q σ : ZMod q).val) := by
  refine ⟨cyc, fun q hq σ μ hμ => ?_⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hζ := zeta_spec q

  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  have hspec : zeta q ^ ((hζ.autToPow ℚ σ : ZMod q).val) = σ (zeta q) := hζ.autToPow_spec ℚ σ
  rw [cyc_of_ne_zero, map_pow, ← hspec, ← pow_mul, ← pow_mul, mul_comm]

end CycQ

theorem solution :
    ∃ cyc : (q : ℕ) → ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ),
      ∀ q : ℕ, q.Prime → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
        μ ^ q = 1 → σ μ = μ ^ ((cyc q σ : ZMod q).val) :=
  CycQ.main
