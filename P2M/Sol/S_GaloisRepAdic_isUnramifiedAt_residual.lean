import Definitions.Def_GaloisRep_Adic
import P2M.Util
namespace P2MW.S_GaloisRepAdic_isUnramifiedAt_residual

theorem solution {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {q : ℕ} (h : ρ.IsUnramifiedAt q) : ρ.residual.IsUnramifiedAt q := by
  intro P hP σ hσ
  show (ρ.ρ σ).baseChange (IsLocalRing.ResidueField A) = 1
  rw [h P hP σ hσ, LinearMap.baseChange_one]
