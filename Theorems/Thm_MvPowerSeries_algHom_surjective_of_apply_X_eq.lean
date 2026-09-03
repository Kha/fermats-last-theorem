import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_MvPowerSeries_algHom_surjective_of_apply_X_eq

universe u v w
theorem MvPowerSeries.algHom_surjective_of_apply_X_eq {σ : Type u} {𝒪 : Type v} {A : Type w} [Finite σ] [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] [IsLocalRing A] [IsNoetherianRing A] (φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A) (a : σ → A) (hφ : ∀ i, φ (MvPowerSeries.X i) = a i) (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) (h𝒪 : Function.Surjective (⇑(Ideal.Quotient.mk (Ideal.span (Set.range a))) ∘ ⇑(algebraMap 𝒪 A))) : Function.Surjective φ := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_algHom_surjective_of_apply_X_eq.solution
