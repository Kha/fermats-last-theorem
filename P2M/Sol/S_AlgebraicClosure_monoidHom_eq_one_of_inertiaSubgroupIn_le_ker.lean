import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le
import P2M.Util
namespace P2MW.S_AlgebraicClosure_monoidHom_eq_one_of_inertiaSubgroupIn_le_ker

theorem solution {Γ : Type*} [Group Γ]
    (χ : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* Γ)
    (hopen : IsOpen (χ.ker : Set ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))))
    (hunr : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      A.inertiaSubgroupIn ℚ ≤ χ.ker) :
    χ = 1 := by
  have hker : χ.ker = ⊤ :=
    AlgebraicClosure.subgroup_eq_top_of_inertiaSubgroupIn_le χ.ker hopen hunr
  ext σ
  have hσ : σ ∈ χ.ker := hker ▸ Subgroup.mem_top σ
  simpa [MonoidHom.mem_ker] using hσ
