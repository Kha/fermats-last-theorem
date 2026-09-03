import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing instTopologicallyFGOfFiniteType
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'

set_option autoImplicit false

open MvPowerSeries

universe u

theorem MvFormalGroup.Hom.exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] {d : ℕ}
    (Ψ Φ : MvFormalGroup d k) [Ψ.IsComm] [Φ.IsComm] (ψ : Ψ.Hom Φ)
    (hfin : Module.Finite k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries))) :
    ∃ (Ψ' : MvFormalGroup d k) (_ : Ψ'.IsComm) (π : Ψ.Hom Ψ')
      (ρ : Ψ'.Hom (Ψ.map (frobenius k p))) (ψ' : Ψ'.Hom Φ),
      (∀ i, (ψ'.comp π).toPowerSeries i = ψ.toPowerSeries i) ∧
      (∀ i, (ρ.comp π).toPowerSeries i = (X i : MvPowerSeries (Fin d) k) ^ p) ∧
      (MvFormalGroup.linearPart ρ.toPowerSeries).rank =
        d - (MvFormalGroup.linearPart ψ.toPowerSeries).rank ∧
      Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range π.toPowerSeries)) =
        p ^ (d - (MvFormalGroup.linearPart ψ.toPowerSeries).rank) ∧
      Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ρ.toPowerSeries)) ∧
      Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ'.toPowerSeries)) ∧
      Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) =
        p ^ (d - (MvFormalGroup.linearPart ψ.toPowerSeries).rank) *
          Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ'.toPowerSeries)) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul.solution
