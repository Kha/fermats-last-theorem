import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_coeff_subst_iterate_sum_single_eq_constantCoeff_invariantDerivation_iterate
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast

open MvPowerSeries

universe u

theorem MvFormalGroup.coeff_subst_iterate_sum_single_eq_constantCoeff_invariantDerivation_iterate
    {𝓞 : Type u} [CommRing 𝓞] {d : ℕ} (F : MvFormalGroup d 𝓞)
    (G : (n : ℕ) → Fin d → MvPowerSeries (Fin n × Fin d) 𝓞)
    (hG1 : ∀ k, G 1 k = X ((0 : Fin 1), k))
    (hGsucc : ∀ (n : ℕ) (k : Fin d), G (n + 1) k =
      subst (Sum.elim
        (fun j => subst (fun sj : Fin n × Fin d => (X (Fin.castSucc sj.1, sj.2) :
          MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)) (G n j))
        (fun j => (X (Fin.last n, j) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)))
        (F.toPowerSeries k))
    (i : Fin d) (L : MvPowerSeries (Fin d) 𝓞 → MvPowerSeries (Fin d) 𝓞)
    (hL : ∀ (H : MvPowerSeries (Fin d) 𝓞) (a : Fin d →₀ ℕ),
      (L H).coeff a = (subst F.toPowerSeries H).coeff (a.sumElim (Finsupp.single i 1)))
    (n : ℕ) (hn : 1 ≤ n) (H : MvPowerSeries (Fin d) 𝓞) :
    (subst (G n) H).coeff (∑ s : Fin n, Finsupp.single (s, i) 1) = (L^[n] H).constantCoeff := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_coeff_subst_iterate_sum_single_eq_constantCoeff_invariantDerivation_iterate.solution
