import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import P2M.Util
import P2M.Sol.S_MvPowerSeries_annihilator_ker_eq_span_det

universe u v w x
theorem MvPowerSeries.annihilator_ker_eq_span_det
    {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (n : ℕ) (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) 𝒪))
    (f : Fin n → MvPowerSeries (Fin n) 𝒪) (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f))]
    [Module.Free 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f))]
    (π : (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) →ₐ[𝒪] 𝒪)
    (hπ : (π : _ →+* 𝒪).comp (Ideal.Quotient.mk (Ideal.span (Set.range f))) =
      MvPowerSeries.constantCoeff) :
    (RingHom.ker π).annihilator =
        Ideal.span {Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det} ∧
      (RingHom.ker π).annihilator.map π =
        Ideal.span {(g.map MvPowerSeries.constantCoeff).det} := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_annihilator_ker_eq_span_det.solution
