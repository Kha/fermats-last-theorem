import Mathlib
import Theorems.Thm_Module_exists_surjective_linearMap_ext_of_exact_of_free
import Theorems.Thm_Module_subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal
import P2M.Util
namespace P2MW.S_Module_length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact

set_option autoImplicit false

universe u

open TensorProduct
open CategoryTheory

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (n : ℕ) (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hlen : rs.length = n + 1)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)]
    (hbdd : ∀ i, n + 1 < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (hex0 : ∀ z : K 0, δ 0 z = 0 → z = 0)
    (hex : ∀ i, i < n → ∀ z : K (i + 1), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i))
    (htors : ∃ N : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal R ^ N, ∀ q : K (n + 1) ⧸ LinearMap.range (δ n), a • q = 0) :
    Module.length R (K (n + 1) ⧸ LinearMap.range (δ n)) =
      Module.length R (Module.Dual R (K 0) ⧸ LinearMap.range (δ 0).dualMap) := by

  obtain ⟨⟨π, hπsurj, hπker⟩, -⟩ :=
    Module.exists_surjective_linearMap_ext_of_exact_of_free R n K δ hdd hex0 hex R

  obtain ⟨-, hlenExt⟩ :=
    Module.subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal R rs
      hreg.toIsWeaklyRegular hmax (K (n + 1) ⧸ LinearMap.range (δ n)) htors
  rw [hlen] at hlenExt
  rw [← hlenExt, ← LinearEquiv.length_eq (π.quotKerEquivOfSurjective hπsurj), hπker]
  rfl
