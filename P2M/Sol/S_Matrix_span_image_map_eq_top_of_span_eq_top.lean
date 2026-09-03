import Mathlib
import P2M.Util
namespace P2MW.S_Matrix_span_image_map_eq_top_of_span_eq_top

open IsLocalRing

theorem solution
    {n : Type*} [Fintype n] [DecidableEq n]
    {k : Type*} [Field k] {K : Type*} [Field K] (f : k →+* K)
    {S : Set (Matrix n n k)} (hS : Submodule.span k S = ⊤) :
    Submodule.span K ((fun X : Matrix n n k => X.map f) '' S) = ⊤ := by
  have key : ∀ X ∈ Submodule.span k S,
      X.map f ∈ Submodule.span K ((fun X : Matrix n n k => X.map f) '' S) := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have h0 : (0 : Matrix n n k).map f = 0 := by
        ext i j; simp
      rw [h0]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have hadd : (x + y).map f = x.map f + y.map f := by
        ext i j; simp
      rw [hadd]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have hsmul : (a • x).map f = f a • x.map f := by
        ext i j
        simp [Matrix.map_apply, smul_eq_mul]
      rw [hsmul]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  rintro M -
  have hM : M = ∑ i, ∑ j, M i j • Matrix.single i j (1 : K) := by
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.matrix_eq_sum_single M
  rw [hM]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ ?_
  have hsingle : Matrix.single i j (1 : K) = (Matrix.single i j (1 : k)).map f := by
    rw [Matrix.map_single, map_one]
  rw [hsingle]
  exact key _ (hS ▸ Submodule.mem_top)
