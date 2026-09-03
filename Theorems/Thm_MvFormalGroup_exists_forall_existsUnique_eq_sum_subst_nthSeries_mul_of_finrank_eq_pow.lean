import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_forall_existsUnique_eq_sum_subst_nthSeries_mul_of_finrank_eq_pow
attribute [-instance] instTopologicallyFGOfFiniteType

open MvPowerSeries hiding finite_flat_exists_basis_substAlgHom_of_finite_quotient

universe u v

theorem MvFormalGroup.exists_forall_existsUnique_eq_sum_subst_nthSeries_mul_of_finrank_eq_pow
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm] (h : ℕ)
    (hh : Module.finrank (𝓞 ⧸ Ideal.span {(p : 𝓞)})
      (MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {(p : 𝓞)}) ⧸
        Ideal.span (Set.range ((Φ.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))).nthSeries p))) =
      p ^ h)
    (v : ℕ) :
    ∃ e : Fin (p ^ (v * h)) → MvPowerSeries (Fin d) 𝓞,
      ∀ F : MvPowerSeries (Fin d) 𝓞, ∃! c : Fin (p ^ (v * h)) → MvPowerSeries (Fin d) 𝓞,
        F = ∑ j, MvPowerSeries.subst (Φ.nthSeries (p ^ v)) (c j) * e j := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_forall_existsUnique_eq_sum_subst_nthSeries_mul_of_finrank_eq_pow.solution
