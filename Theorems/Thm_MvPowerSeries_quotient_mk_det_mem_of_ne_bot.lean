import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import P2M.Util
import P2M.Sol.S_MvPowerSeries_quotient_mk_det_mem_of_ne_bot

universe u
theorem MvPowerSeries.quotient_mk_det_mem_of_ne_bot
    {k : Type u} [Field k] {n : ℕ} (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) k))
    (f : Fin n → MvPowerSeries (Fin n) k) (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))] :
    Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ≠ 0 ∧
      ∀ J : Ideal (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f)), J ≠ ⊥ →
        Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ∈ J := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_quotient_mk_det_mem_of_ne_bot.solution
