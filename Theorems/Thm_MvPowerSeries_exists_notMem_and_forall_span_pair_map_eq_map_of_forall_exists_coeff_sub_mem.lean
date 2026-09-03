import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_notMem_and_forall_span_pair_map_eq_map_of_forall_exists_coeff_sub_mem

set_option autoImplicit false

open scoped BigOperators

theorem MvPowerSeries.exists_notMem_and_forall_span_pair_map_eq_map_of_forall_exists_coeff_sub_mem
    {R : Type} [CommRing R] [IsNoetherianRing R] (J : Ideal (MvPowerSeries (Fin 2) R))
    (hproj : Module.Projective R (MvPowerSeries (Fin 2) R ⧸ J))
    (𝔫 : Ideal R) (h𝔫 : 𝔫 ≠ ⊤)
    (r : Fin 2 → MvPowerSeries (Fin 2) R) (hr : ∀ j, r j ∈ J)
    (hgen : ∀ f ∈ J, ∃ (a b : Fin 2 → MvPowerSeries (Fin 2) R), (∀ i, b i ∈ J) ∧
      ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d (f - (∑ j, a j * r j + ∑ i, MvPowerSeries.X i * b i)) ∈ 𝔫) :
    ∃ g : R, g ∉ 𝔫 ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], IsUnit (algebraMap R R' g) →
      Ideal.span (Set.range fun j => MvPowerSeries.map (algebraMap R R') (r j)) =
        J.map (MvPowerSeries.map (algebraMap R R')) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_notMem_and_forall_span_pair_map_eq_map_of_forall_exists_coeff_sub_mem.solution
