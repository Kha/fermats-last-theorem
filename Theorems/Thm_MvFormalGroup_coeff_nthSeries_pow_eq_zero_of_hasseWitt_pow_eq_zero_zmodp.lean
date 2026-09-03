import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'

open MvPowerSeries

universe u

theorem MvFormalGroup.coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp
    (p : ℕ) [Fact p.Prime] {d : ℕ} (F : MvFormalGroup d (ZMod p)) [F.IsComm]
    (ν : ℕ)
    (hB : (Matrix.of fun i j : Fin d => (F.nthSeries p i).coeff (Finsupp.single j p)) ^ ν = 0)
    (i : Fin d) (m : Fin d →₀ ℕ) (hm : ∃ j, ¬ p ^ (ν + 1) ∣ m j) :
    (F.nthSeries (p ^ ν) i).coeff m = 0 := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp.solution
