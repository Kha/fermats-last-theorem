import Definitions.Def_Gamma0HeckeOperatorHom
import Theorems.Thm_HeckeEis_heckeOperatorHom_apply_of_factorsThroughEntry
import P2M.Util
namespace P2MW.S_HeckeEis_heckeOperatorHom_eq_of_factorsThroughEntry

theorem solution (N : ℕ) {ℓ : ℕ} [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hfac : ∀ γ δ : CongruenceSubgroup.Gamma0 N,
      CongruenceSubgroup.Gamma0Map N γ = CongruenceSubgroup.Gamma0Map N δ →
        φ (Additive.ofMul γ) = φ (Additive.ofMul δ)) :
    HeckeEis.heckeOperatorHom N ℓ A φ = (ℓ + 1) • φ := by
  refine AddMonoidHom.ext fun x => ?_
  rw [AddMonoidHom.nsmul_apply, ← ofMul_toMul x]
  exact HeckeEis.heckeOperatorHom_apply_of_factorsThroughEntry N A hℓ hℓN φ hfac x.toMul
