import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_finrank_quotient_span_nthSeries_pow_eq_pow
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid instTopologicallyFGOfFiniteType
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast

p2m_open "MvPowerSeries~finite_flat_exists_basis_substAlgHom_of_finite_quotient"

universe u

theorem MvFormalGroup.finrank_quotient_span_nthSeries_pow_eq_pow
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] {d : ℕ} (F : MvFormalGroup d k) [F.IsComm] (h : ℕ)
    (hh : Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (F.nthSeries p))) = p ^ h)
    (v : ℕ) :
    Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) =
      p ^ (v * h) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_finrank_quotient_span_nthSeries_pow_eq_pow.solution
