import Mathlib
import Definitions.Def_ModularCurve_JZeroTateModule
import P2M.Util
import P2M.Sol.S_TateModule_exists_rationalTateModule_linearEquiv_comp_rationalGaloisRep_eq_of_injective_of_card_torsionBy_eq

set_option autoImplicit false

open scoped TensorProduct

theorem TateModule.exists_rationalTateModule_linearEquiv_comp_rationalGaloisRep_eq_of_injective_of_card_torsionBy_eq
    {J J' : Type} [AddCommGroup J] [AddCommGroup J'] {G : Type} [Monoid G] [DistribMulAction G J] [DistribMulAction G J']
    (β : J →+ J') (hβ : Function.Injective β) (hβG : ∀ (g : G) (x : J), β (g • x) = g • β x)
    (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ)
    (hJ : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ J ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ r)
    (hJ' : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ J' ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ r) :
    ∃ (T : TateModule ℓ J →ₗ[ℤ_[ℓ]] TateModule ℓ J')
      (e : ModularCurve.RationalTateModule ℓ J ≃ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ J'),
      (∀ (x : TateModule ℓ J) (n : ℕ), ((T x : TateModule ℓ J') : ℕ → J') n = β ((x : ℕ → J) n)) ∧
      (∀ v, e v = T.baseChange ℚ_[ℓ] v) ∧
      ∀ g : G, (e : ModularCurve.RationalTateModule ℓ J →ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ J') ∘ₗ
          ModularCurve.rationalGaloisRep ℓ J G g =
        ModularCurve.rationalGaloisRep ℓ J' G g ∘ₗ
          (e : ModularCurve.RationalTateModule ℓ J →ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ J') := by p2m_exact_reverting @_root_.P2MW.S_TateModule_exists_rationalTateModule_linearEquiv_comp_rationalGaloisRep_eq_of_injective_of_card_torsionBy_eq.solution
