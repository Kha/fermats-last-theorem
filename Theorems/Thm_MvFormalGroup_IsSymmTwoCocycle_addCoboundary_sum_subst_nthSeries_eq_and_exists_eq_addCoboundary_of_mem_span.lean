import Mathlib
import Definitions.Def_MvFormalGroup_TwoCocycle
import P2M.Util
import P2M.Sol.S_MvFormalGroup_IsSymmTwoCocycle_addCoboundary_sum_subst_nthSeries_eq_and_exists_eq_addCoboundary_of_mem_span
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing instTopologicallyFGOfFiniteType
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'

set_option autoImplicit false

universe u

theorem MvFormalGroup.IsSymmTwoCocycle.addCoboundary_sum_subst_nthSeries_eq_and_exists_eq_addCoboundary_of_mem_span
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {n : ℕ} {F₀ : MvFormalGroup n k} [F₀.IsComm] (h : ℕ)
    (hh : Module.finrank k (MvPowerSeries (Fin n) k ⧸
      Ideal.span (Set.range (F₀.nthSeries p))) = p ^ h)
    {Γ : MvPowerSeries (Fin n ⊕ Fin n) k} (hΓ : F₀.IsSymmTwoCocycle Γ) :
    F₀.addCoboundary (∑ i ∈ Finset.range p,
        MvPowerSeries.subst (Sum.elim (F₀.nthSeries i) fun l => MvPowerSeries.X l) Γ) =
      MvPowerSeries.subst (Sum.elim
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k))
          (F₀.nthSeries p i))
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k))
          (F₀.nthSeries p i))) Γ ∧
    ((∑ i ∈ Finset.range p,
        MvPowerSeries.subst (Sum.elim (F₀.nthSeries i) fun l => MvPowerSeries.X l) Γ) ∈
        Ideal.span (Set.range (F₀.nthSeries p)) →
      ∃ g : MvPowerSeries (Fin n) k, MvPowerSeries.constantCoeff g = 0 ∧
        Γ = F₀.addCoboundary g) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_IsSymmTwoCocycle_addCoboundary_sum_subst_nthSeries_eq_and_exists_eq_addCoboundary_of_mem_span.solution
