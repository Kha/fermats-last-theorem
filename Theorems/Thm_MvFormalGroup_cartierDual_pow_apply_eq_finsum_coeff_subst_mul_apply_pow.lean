import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_MvFormalGroup_cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast

set_option autoImplicit false

universe u v

open scoped TensorProduct

theorem MvFormalGroup.cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {n : ℕ} (F : MvFormalGroup n k) [F.IsComm]
    (V : Fin n → MvPowerSeries (Fin n) k) (hV0 : ∀ i, MvPowerSeries.constantCoeff (V i) = 0)
    (hV : ∀ i, MvPowerSeries.subst (fun l => (MvPowerSeries.X l : MvPowerSeries (Fin n) k) ^ p) (V i) =
      F.nthSeries p i)
    {L : Type v} [CommRing L] [HopfAlgebra k L] [Module.Finite k L]
    (π : MvPowerSeries (Fin n) k →ₐ[k] L)
    (Θ : MvPowerSeries (Fin n ⊕ Fin n) k →ₐ[k] L ⊗[k] L)
    (hΘl : ∀ G : MvPowerSeries (Fin n) k, Θ (MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) G) = π G ⊗ₜ[k] 1)
    (hΘr : ∀ G : MvPowerSeries (Fin n) k, Θ (MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) G) = 1 ⊗ₜ[k] π G)
    (hcomul : ∀ G, Coalgebra.comul (R := k) (π G) = Θ (MvPowerSeries.subst F.toPowerSeries G))
    (hcounit : ∀ G, Coalgebra.counit (R := k) (π G) = MvPowerSeries.constantCoeff G)
    (φ : CartierDual k L) (g : MvPowerSeries (Fin n) k) :
    (φ ^ p) (π g) = ∑ᶠ a : Fin n →₀ ℕ,
      MvPowerSeries.coeff a (MvPowerSeries.subst V g) * φ (π (MvPowerSeries.monomial a (1 : k))) ^ p := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow.solution
