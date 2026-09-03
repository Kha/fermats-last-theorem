import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_Hom_exists_finrank_quotient_span_range_map_eq_prime_pow_of_isComm
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing instTopologicallyFGOfFiniteType
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'

set_option autoImplicit false

open MvPowerSeries

universe u

theorem MvFormalGroup.Hom.exists_finrank_quotient_span_range_map_eq_prime_pow_of_isComm
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] {d : ℕ}
    (Φ Φ' : MvFormalGroup d k) [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ')
    (hfin : Module.Finite k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range φ.toPowerSeries))) :
    ∃ h : ℕ, ∀ (κ : Type u) [Field κ] (f : k →+* κ),
      Module.finrank κ (MvPowerSeries (Fin d) κ ⧸
        Ideal.span (Set.range fun i => MvPowerSeries.map f (φ.toPowerSeries i))) = p ^ h := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_Hom_exists_finrank_quotient_span_range_map_eq_prime_pow_of_isComm.solution
