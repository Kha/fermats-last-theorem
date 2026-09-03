import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker

set_option autoImplicit false

p2m_open "ModularCurve~exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even ModularCurve.FullLevel"

open scoped MatrixGroups ModularForm

theorem ModularCurve.FullLevel.exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker
    (m : ℕ) [NeZero m] (M' : ℕ) [NeZero M'] (hmM' : Nat.Coprime m M')
    (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH m M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (m ^ 2))).ker)
    {k : ℤ} (hk : Even k)
    (f : ModularForm (CohCarrier.GammaH (m ^ 2 * M') H₁ : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') :
    ∃ h : ℕ → ModularForm (CohCarrier.GammaH (m ^ 2 * M') H₁ : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ j n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 (h j)).coeff n = (r : ℂ)) ∧
      ∀ (s : ℕ) (γ' : SL(2, ℤ)), Nat.Coprime s m → γ' ∈ CongruenceSubgroup.Gamma0 M' →
        ((γ' 1 1 : ℤ) : ZMod ℓg) = ((γ 1 1 : ℤ) : ZMod ℓg) →
        !![(1 : ZMod m), 0; 0, (s : ZMod m)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m)
          = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m) * !![(1 : ZMod m), 0; 0, (s : ZMod m)] →
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] ModularCurve.FullLevel.conjElemN m γ') =
          ∑ j ∈ Finset.range m,
            Complex.exp (2 * Real.pi * Complex.I * ((s * j : ℕ) : ℂ) / m) •
              (⇑(h j) : UpperHalfPlane → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker.solution
