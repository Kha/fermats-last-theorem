import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
namespace P2MW.S_QuaternionAlgebra_IsOrder_forall_exists_smul_add_mul_iff_mul_of_isUnitOf_right

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem solution
    {a b : ℚ} {N : ℕ} (Λ R J' : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R) (hRΛ : R ≤ Λ)
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (ℓ : ℕ) (t v : ℍ[ℚ, a, b]) (ht : t ∈ R) (hv : v ∈ R)
    (hv' : ∃ v' : ℍ[ℚ, a, b], v' ∈ R ∧ v * v' = 1 ∧ v' * v = 1)
    (hlev : ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) :
    t * v ∈ R ∧ nrd (t * v) = nrd t * nrd v ∧
      ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * (t * v) = x) ↔ ∃ j ∈ J', j * (t * v) = x := by
  obtain ⟨v', hv'R, hvv', hv'v⟩ := hv'
  obtain ⟨-, -, -, -, h5⟩ := hJ'

  have hJv : ∀ y ∈ J', y * v ∈ J' := fun y hy => (h5 v (hRΛ hv)).mp hv y hy
  have hJv' : ∀ y ∈ J', y * v' ∈ J' := fun y hy => (h5 v' (hRΛ hv'R)).mp hv'R y hy
  refine ⟨hR.mul_mem ht hv, ?_, fun x => ⟨?_, ?_⟩⟩
  ·
    simp only [nrd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
      QuaternionAlgebra.imK_mul]
    ring
  · rintro ⟨j, hj, m, hm, rfl⟩

    obtain ⟨j₂, hj₂, hj₂e⟩ := (hlev ((ℓ : ℤ) • (j * v') + m * t)).mp ⟨j * v', hJv' j hj, m, hm, rfl⟩
    refine ⟨j₂, hj₂, ?_⟩
    calc j₂ * (t * v) = (j₂ * t) * v := (mul_assoc _ _ _).symm
      _ = ((ℓ : ℤ) • (j * v') + m * t) * v := by rw [hj₂e]
      _ = (ℓ : ℤ) • j + m * (t * v) := by
          rw [add_mul, smul_mul_assoc, mul_assoc j v' v, hv'v, mul_one, mul_assoc]
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨j₁, hj₁, m, hm, he⟩ := (hlev (j * t)).mpr ⟨j, hj, rfl⟩
    refine ⟨j₁ * v, hJv j₁ hj₁, m, hm, ?_⟩
    calc (ℓ : ℤ) • (j₁ * v) + m * (t * v) = ((ℓ : ℤ) • j₁ + m * t) * v := by
          rw [add_mul, smul_mul_assoc, mul_assoc]
      _ = (j * t) * v := by rw [he]
      _ = j * (t * v) := mul_assoc _ _ _
