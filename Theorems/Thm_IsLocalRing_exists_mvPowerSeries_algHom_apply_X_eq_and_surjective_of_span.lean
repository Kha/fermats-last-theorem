import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span

universe u v
open IsLocalRing
theorem IsLocalRing.exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span
    {𝒪 : Type u} {R : Type v} [CommRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    [CommRing R] [Algebra 𝒪 R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap 𝒪 R)))
    {r : ℕ} (a : Fin r → R) (ha : ∀ i, a i ∈ maximalIdeal R)
    (hgen : maximalIdeal R ≤
      Ideal.span (Set.range a) ⊔ maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝒪).map (algebraMap 𝒪 R)) :
    ∃ ψ : MvPowerSeries (Fin r) 𝒪 →ₐ[𝒪] R, (∀ i, ψ (MvPowerSeries.X i) = a i) ∧ Function.Surjective ψ := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span.solution
