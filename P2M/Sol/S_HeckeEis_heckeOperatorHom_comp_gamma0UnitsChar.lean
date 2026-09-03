import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0UnitsChar
import Theorems.Thm_HeckeEis_heckeOperatorHom_eq_of_factorsThroughEntry
import P2M.Util
namespace P2MW.S_HeckeEis_heckeOperatorHom_comp_gamma0UnitsChar

theorem solution (N : ℕ) {ℓ : ℕ} [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (χ : Additive (ZMod N)ˣ →+ A) :
    HeckeEis.heckeOperatorHom N ℓ A (χ.comp (Ihara.gamma0UnitsChar N)) =
      (ℓ + 1) • χ.comp (Ihara.gamma0UnitsChar N) := by
  refine HeckeEis.heckeOperatorHom_eq_of_factorsThroughEntry N A hℓ hℓN _ fun γ δ h => ?_
  show χ (Ihara.gamma0UnitsChar N (Additive.ofMul γ)) = χ (Ihara.gamma0UnitsChar N (Additive.ofMul δ))
  have hu : Ihara.gamma0UnitsHom N γ = Ihara.gamma0UnitsHom N δ := Units.ext h
  rw [Ihara.gamma0UnitsChar_apply, Ihara.gamma0UnitsChar_apply, toMul_ofMul, toMul_ofMul, hu]
