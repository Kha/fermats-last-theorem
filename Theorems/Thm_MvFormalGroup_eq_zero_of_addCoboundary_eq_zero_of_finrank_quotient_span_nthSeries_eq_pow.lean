import Mathlib
import Definitions.Def_MvFormalGroup_TwoCocycle
import P2M.Util
import P2M.Sol.S_MvFormalGroup_eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid instTopologicallyFGOfFiniteType
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast

set_option autoImplicit false

universe u

theorem MvFormalGroup.eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {n : ℕ} (F₀ : MvFormalGroup n k) (h : ℕ)
    (hh : Module.finrank k (MvPowerSeries (Fin n) k ⧸
      Ideal.span (Set.range (F₀.nthSeries p))) = p ^ h)
    (f : MvPowerSeries (Fin n) k) (hf0 : MvPowerSeries.constantCoeff f = 0)
    (hf : F₀.addCoboundary f = 0) : f = 0 := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow.solution
