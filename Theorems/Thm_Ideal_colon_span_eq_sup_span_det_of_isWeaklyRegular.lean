import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import P2M.Util
import P2M.Sol.S_Ideal_colon_span_eq_sup_span_det_of_isWeaklyRegular

universe u
theorem Ideal.colon_span_eq_sup_span_det_of_isWeaklyRegular
    {P : Type u} [CommRing P] {n : ℕ} (x f : Fin n → P) (g : Matrix (Fin n) (Fin n) P)
    (hf : ∀ i, f i = ∑ j, g i j * x j)
    (hy : ∃ y : Fin n → P, RingTheory.Sequence.IsWeaklyRegular P (List.ofFn y) ∧
      ∀ i, y i ∈ Ideal.span (Set.range f)) :
    (Ideal.span (Set.range f)).colon (Ideal.span (Set.range x)) =
        Ideal.span (Set.range f) ⊔ Ideal.span {g.det} ∧
      (Ideal.span (Set.range f)).colon (Ideal.span {g.det}) = Ideal.span (Set.range x) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_colon_span_eq_sup_span_det_of_isWeaklyRegular.solution
