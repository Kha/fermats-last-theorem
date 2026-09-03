import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_Hom_eq_of_map_eq_of_ker_pow_eq_bot_of_finrank_eq_pow
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing instTopologicallyFGOfFiniteType
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'

set_option autoImplicit false

universe u

theorem MvFormalGroup.Hom.eq_of_map_eq_of_ker_pow_eq_bot_of_finrank_eq_pow
    {R k : Type u} [CommRing R] [Field k] (π : R →+* k) (hπ : Function.Surjective π)
    (μ : ℕ) (hI : RingHom.ker π ^ (μ + 1) = ⊥) (p : ℕ) [Fact p.Prime] [CharP k p]
    {m n : ℕ} (F : MvFormalGroup m R) [F.IsComm] (G : MvFormalGroup n R) [G.IsComm] (h : ℕ)
    (hh : Module.finrank k (MvPowerSeries (Fin m) k ⧸
      Ideal.span (Set.range ((F.map π).nthSeries p))) = p ^ h)
    (θ₁ θ₂ : F.Hom G)
    (heq : ∀ i, MvPowerSeries.map π (θ₁.toPowerSeries i) = MvPowerSeries.map π (θ₂.toPowerSeries i)) :
    θ₁ = θ₂ := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_Hom_eq_of_map_eq_of_ker_pow_eq_bot_of_finrank_eq_pow.solution
