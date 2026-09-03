import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Theorems.Thm_Module_Invertible_range_le_smul_top_or_of_comp_eq_smul
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_mem_stratum0_or_mem_stratum1

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega LT.LatticeTree

open scoped PadicInt Padic

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra ℤ_[p] B] (hB : IsNilpotent (p : B))
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (x : PrimeSpectrum B) :
    x ∈ Q.stratum₀ ∨ x ∈ Q.stratum₁ := by
  haveI := Q.invertible₀
  haveI := Q.invertible₁
  have hp : algebraMap ℤ_[p] B (p : ℤ_[p]) ∈ x.asIdeal := by
    rw [map_natCast]
    obtain ⟨n, hn⟩ := hB
    exact x.2.mem_of_pow_mem n (by rw [hn]; exact x.asIdeal.zero_mem)
  have hfg : Q.Pi₁ ∘ₗ Q.Pi₀ = algebraMap ℤ_[p] B (p : ℤ_[p]) • LinearMap.id := by
    ext t
    exact Q.Pi₁_Pi₀ t
  exact Module.Invertible.range_le_smul_top_or_of_comp_eq_smul Q.Pi₀ Q.Pi₁ _ hfg x hp
