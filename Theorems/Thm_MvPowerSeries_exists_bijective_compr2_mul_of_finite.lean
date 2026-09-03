import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_bijective_compr2_mul_of_finite

universe u v w x

theorem MvPowerSeries.exists_bijective_compr2_mul_of_finite {k : Type u} [Field k] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) k)) (f : Fin n → MvPowerSeries (Fin n) k)
    (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))] :
    ∃ l : (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f)) →ₗ[k] k,
      Function.Bijective ((LinearMap.mul k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))).compr₂ l) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_bijective_compr2_mul_of_finite.solution
