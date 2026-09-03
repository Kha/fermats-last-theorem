import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_algHom_apply_X_eq

universe u v w
theorem MvPowerSeries.exists_algHom_apply_X_eq {σ : Type u} {𝒪 : Type v} {A : Type w} [Finite σ] [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] (I : Ideal A) [IsAdicComplete I A] (a : σ → A) (ha : ∀ i, a i ∈ I) : ∃ φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A, ∀ i, φ (MvPowerSeries.X i) = a i := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_algHom_apply_X_eq.solution
