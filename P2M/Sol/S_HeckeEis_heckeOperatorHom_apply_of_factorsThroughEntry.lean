import Definitions.Def_Gamma0HeckeOperatorHom
import Theorems.Thm_HeckeEis_heckeOperatorHom_apply_of_conj_invariant
import Theorems.Thm_ModularCurve_index_heckeUpper
import P2M.Util
namespace P2MW.S_HeckeEis_heckeOperatorHom_apply_of_factorsThroughEntry

theorem solution (N : ℕ) {ℓ : ℕ} [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hfac : ∀ γ δ : CongruenceSubgroup.Gamma0 N,
      CongruenceSubgroup.Gamma0Map N γ = CongruenceSubgroup.Gamma0Map N δ →
        φ (Additive.ofMul γ) = φ (Additive.ofMul δ))
    (g : CongruenceSubgroup.Gamma0 N) :
    HeckeEis.heckeOperatorHom N ℓ A φ (Additive.ofMul g) = (ℓ + 1) • φ (Additive.ofMul g) := by
  rw [HeckeEis.heckeOperatorHom_apply_of_conj_invariant N ℓ φ (fun γ => hfac _ _ rfl) (Additive.ofMul g),
    ModularCurve.index_heckeUpper hℓ hℓN]
