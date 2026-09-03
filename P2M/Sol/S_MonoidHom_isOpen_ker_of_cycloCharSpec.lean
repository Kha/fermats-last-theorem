import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import P2M.Util
namespace P2MW.S_MonoidHom_isOpen_ker_of_cycloCharSpec

set_option autoImplicit false

theorem solution (m : ℕ) [NeZero m]
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod m)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ m = 1 → σ μ = μ ^ ((cyc σ : ZMod m)).val) :
    IsOpen ((cyc.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by

  haveI : NeZero ((m : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne m)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) m
  have hζ0 : ζ ≠ 0 := (hζ.isUnit (NeZero.ne m)).ne_zero

  have hsub : MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ ≤ cyc.ker := by
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hσ
    have hpow : ζ ^ ((cyc σ : ZMod m)).val = ζ := (hcyc σ ζ hζ.pow_eq_one).symm.trans hσ
    have hz : ζ ^ ((((cyc σ : ZMod m)).val : ℤ) - 1) = 1 := by
      rw [zpow_sub₀ hζ0, zpow_one, zpow_natCast, hpow, div_self hζ0]
    have hdvd : (m : ℤ) ∣ (((cyc σ : ZMod m)).val : ℤ) - 1 := (hζ.zpow_eq_one_iff_dvd _).mp hz
    have hcast : (cyc σ : ZMod m) = 1 := by
      have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (((cyc σ : ZMod m)).val - 1 : ℤ) m).mpr hdvd
      rwa [Int.cast_sub, Int.cast_one, sub_eq_zero, Int.cast_natCast, ZMod.natCast_val,
        ZMod.cast_id] at h0
    exact Units.val_eq_one.mp hcast

  exact Subgroup.isOpen_of_openSubgroup _
    (U := ⟨_, stabilizer_isOpen_of_isIntegral (K := ℚ) (L := AlgebraicClosure ℚ) ζ⟩) hsub

example (m : ℕ) [NeZero m]
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod m)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ m = 1 → σ μ = μ ^ ((cyc σ : ZMod m)).val) :
    IsOpen ((cyc.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
  solution m cyc hcyc

#print axioms solution
