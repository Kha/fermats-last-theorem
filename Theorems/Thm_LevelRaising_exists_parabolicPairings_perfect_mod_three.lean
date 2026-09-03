import Definitions.Def_HeckeEis_DegeneracyTransfers
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_LevelRaising_exists_parabolicPairings_perfect_mod_three
attribute [-instance] ModularCurve.PDPairing.isFreeGroup_inf ModularCurve.PDPairing.instFintypeCusp ModularCurve.PDPairing.iotaDeg0_range_finiteIndex ModularCurve.PDPairing.CentralExt.instInv ModularCurve.PDPairing.CentralExt.instGroup ModularCurve.PDPairing.CentralExt.instMul ModularCurve.PDPairing.CentralExt.instOne ModularCurve.PDPairing.Gamma0Upper_finiteIndex
attribute [-simp] ModularCurve.PDPairing.CentralExt.lift_apply ModularCurve.PDPairing.mem_Gamma0Upper ModularCurve.PDPairing.CentralExt.snd_apply ModularCurve.PDPairing.pairZ_apply ModularCurve.PDPairing.conjUpperMat_apply_11 ModularCurve.PDPairing.sect_snd ModularCurve.PDPairing.conjUpperMat_apply_10

set_option autoImplicit false

open CongruenceSubgroup

theorem LevelRaising.exists_parabolicPairings_perfect_mod_three
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (hTpar : ∀ (M ℓ : ℕ) [NeZero ℓ] (φ : Additive (Gamma0 M) →+ ℤ),
      ModularCurve.Period.IsParabolicHom (Gamma0 M) φ →
        ModularCurve.Period.IsParabolicHom (Gamma0 M) (HeckeEis.heckeOperatorHom M ℓ ℤ φ))
    (hrespar₀ : ∀ y ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      HeckeEis.pullbackHom (Ihara.ι₀ N q) y ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ)
    (hrespar₁ : ∀ y ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      HeckeEis.pullbackHom (Ihara.ι₁ N q) y ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ)
    (hβpar₀ : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ,
      HeckeEis.degeneracyTransfer₀ N q ℤ hq hqN x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
    (hβpar₁ : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ,
      HeckeEis.degeneracyTransfer₁ N q ℤ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ) :
    ∃ (pair₁ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ →ₗ[ℤ] ℤ)
      (pair₀ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ] ℤ),
      ((∀ x, (∀ y, (3 : ℤ) ∣ pair₁ x y) → ∃ x', x = (3 : ℤ) • x') ∧
        (∀ y, (∀ x, (3 : ℤ) ∣ pair₁ x y) → ∃ y', y = (3 : ℤ) • y')) ∧
      ((∀ x, (∀ y, (3 : ℤ) ∣ pair₀ x y) → ∃ x', x = (3 : ℤ) • x') ∧
        (∀ y, (∀ x, (3 : ℤ) ∣ pair₀ x y) → ∃ y', y = (3 : ℤ) • y')) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q →
        ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ,
          pair₁ ⟨HeckeEis.heckeOperatorHom (N * q) ℓ ℤ x, hTpar (N * q) ℓ x x.2⟩ y =
            pair₁ x ⟨HeckeEis.heckeOperatorHom (N * q) ℓ ℤ y, hTpar (N * q) ℓ y y.2⟩) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q →
        ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
          pair₀ ⟨HeckeEis.heckeOperatorHom N ℓ ℤ x, hTpar N ℓ x x.2⟩ y =
            pair₀ x ⟨HeckeEis.heckeOperatorHom N ℓ ℤ y, hTpar N ℓ y y.2⟩) ∧
      (∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ)
        (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
          pair₀ ⟨HeckeEis.degeneracyTransfer₀ N q ℤ hq hqN x, hβpar₀ x x.2⟩ y =
            pair₁ x ⟨HeckeEis.pullbackHom (Ihara.ι₀ N q) y, hrespar₀ y y.2⟩) ∧
      (∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ)
        (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
          pair₀ ⟨HeckeEis.degeneracyTransfer₁ N q ℤ x, hβpar₁ x x.2⟩ y =
            pair₁ x ⟨HeckeEis.pullbackHom (Ihara.ι₁ N q) y, hrespar₁ y y.2⟩) := by p2m_exact_reverting @_root_.P2MW.S_LevelRaising_exists_parabolicPairings_perfect_mod_three.solution
