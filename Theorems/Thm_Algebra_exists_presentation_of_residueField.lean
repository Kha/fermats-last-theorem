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
import P2M.Sol.S_Algebra_exists_presentation_of_residueField

universe u v w x
theorem Algebra.exists_presentation_of_residueField
    {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (hk : ∃ (n : ℕ) (g : Fin n → MvPowerSeries (Fin n) (IsLocalRing.ResidueField 𝒪)),
      Nonempty ((MvPowerSeries (Fin n) (IsLocalRing.ResidueField 𝒪) ⧸ Ideal.span (Set.range g)) ≃ₐ[𝒪]
        (T ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 T)))) :
    ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
      Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_presentation_of_residueField.solution
