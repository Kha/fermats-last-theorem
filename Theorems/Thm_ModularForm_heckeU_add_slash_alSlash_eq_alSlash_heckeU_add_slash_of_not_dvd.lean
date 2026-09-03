import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import P2M.Util
import P2M.Sol.S_ModularForm_heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd

set_option autoImplicit false

open scoped MatrixGroups ModularForm
theorem ModularForm.heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (k : ℤ)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 M)
    (hσℓ : (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) = ℓ)
    (ρ : SL(2, ℤ)) (hρ : ρ ∈ CongruenceSubgroup.Gamma0 M)
    (hρℓ : (((ρ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)) * (ℓ : ZMod (M / p)) = 1)
    (f : UpperHalfPlane → ℂ)
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    ModularForm.heckeU k ℓ (ModularForm.alSlash W k f) +
        (ModularForm.alSlash W k f) ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ) =
      ModularForm.alSlash W k
        (ModularForm.heckeU k ℓ (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ρ : GL (Fin 2) ℝ)) +
          (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ρ : GL (Fin 2) ℝ)) ∣[k]
            ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd.solution
