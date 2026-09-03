import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_MvPowerSeries_algHom_ext_of_apply_X_mem

universe u v w
theorem MvPowerSeries.algHom_ext_of_apply_X_mem {σ : Type u} {𝒪 : Type v} {A : Type w} [Finite σ] [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] (I : Ideal A) [IsHausdorff I A] (φ ψ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A) (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ I) (h : ∀ i, φ (MvPowerSeries.X i) = ψ (MvPowerSeries.X i)) : φ = ψ := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_algHom_ext_of_apply_X_mem.solution
