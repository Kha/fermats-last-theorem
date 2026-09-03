import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem

theorem PowerSeries.exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem
    {E : Type*} [Field E] [CharZero E] (ι : AlgebraicClosure ℚ →+* E)
    (V : Submodule E (PowerSeries E))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A : PowerSeries (AlgebraicClosure ℚ)) (hA : ∀ n : ℕ, PowerSeries.coeff n A ∈ K)
    (hV : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      A.map (ι.comp (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ∈ V) :
    ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (r : Fin n → PowerSeries ℚ),
      (∀ i, (r i).map (algebraMap ℚ E) ∈ V) ∧
        A.map ι = ∑ i, ι (c i) • (r i).map (algebraMap ℚ E) := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem.solution
