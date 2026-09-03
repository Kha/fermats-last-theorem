import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_AuxLevelOne_mul_mul_inv_mem_and_map_fixedField_of_isLevelAutAt_gamma0_of_dvd

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevelOne.mul_mul_inv_mem_and_map_fixedField_of_isLevelAutAt_gamma0_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (G : Subgroup (↥K ≃ₐ[L] ↥K))
    (hG : G = Subgroup.closure {τ : ↥K ≃ₐ[L] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ})
    (K₀ : IntermediateField L ↥K) (hK₀ : K₀ = IntermediateField.fixedField G)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ) :
    (∀ σ : ↥K ≃ₐ[L] ↥K, σ ∈ G → τ * σ * τ⁻¹ ∈ G) ∧
    (∀ σ : ↥K ≃ₐ[L] ↥K, σ ∈ G → τ⁻¹ * σ * τ ∈ G) ∧
    (∀ f : ↥K, f ∈ K₀ → τ f ∈ K₀) ∧
    (∀ f : ↥K, f ∈ K₀ → τ.symm f ∈ K₀) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_AuxLevelOne_mul_mul_inv_mem_and_map_fixedField_of_isLevelAutAt_gamma0_of_dvd.solution
