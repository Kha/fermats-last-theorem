import Mathlib
import P2M.Util
namespace P2MW.S_Matrix_exists_eq_smul_one_of_commute_of_span_eq_top

theorem solution {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A]
    {S : Set (Matrix n n A)} (hS : Submodule.span A S = ⊤)
    (M : Matrix n n A) (hM : ∀ X ∈ S, X * M = M * X) :
    ∃ a : A, M = a • 1 := by
  have hcomm : ∀ X : Matrix n n A, X * M = M * X := by
    have hle : Submodule.span A S ≤
        { carrier := {X | X * M = M * X}
          add_mem' := fun {X} {Y} hX hY => by
            simp only [Set.mem_setOf_eq] at hX hY ⊢
            rw [add_mul, mul_add, hX, hY]
          zero_mem' := by simp
          smul_mem' := fun a X hX => by
            simp only [Set.mem_setOf_eq] at hX ⊢
            rw [smul_mul_assoc, mul_smul_comm, hX] } :=
      Submodule.span_le.mpr hM
    intro X
    exact hle (hS ▸ Submodule.mem_top)
  have hMc : M ∈ Set.center (Matrix n n A) := Semigroup.mem_center_iff.mpr hcomm
  rw [Matrix.center_eq_range] at hMc
  obtain ⟨a, ha⟩ := hMc
  refine ⟨a, ?_⟩
  rw [← ha, Matrix.scalar_apply]
  ext i j
  simp [Matrix.one_apply, Matrix.diagonal_apply, Matrix.smul_apply, mul_comm]
