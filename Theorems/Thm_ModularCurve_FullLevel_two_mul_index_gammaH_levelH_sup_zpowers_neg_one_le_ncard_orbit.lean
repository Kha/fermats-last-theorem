import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_le_ncard_orbit
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.two_mul_index_gammaH_levelH_sup_zpowers_neg_one_le_ncard_orbit
    (N₀ : ℕ) (hN₀ : 3 ≤ N₀) (M' : ℕ) [NeZero M'] (hcop : Nat.Coprime N₀ M')
    (V : Type) [AddCommGroup V]
    (B₁ B₂ : V) (hB₁ : (N₀ * M') • B₁ = 0) (hB₂ : (N₀ * M') • B₂ = 0)
    (hBi : ∀ a b : ℤ, a • B₁ + b • B₂ = 0 → ((N₀ * M' : ℕ) : ℤ) ∣ a ∧ ((N₀ * M' : ℕ) : ℤ) ∣ b)
    (hBs : ∀ v : V, (N₀ * M') • v = 0 → ∃ a b : ℤ, v = a • B₁ + b • B₂)
    (P₁ P₂ : V) (hP₁ : N₀ • P₁ = 0) (hP₂ : N₀ • P₂ = 0)
    (hPi : ∀ a b : ℤ, a • P₁ + b • P₂ = 0 → (N₀ : ℤ) ∣ a ∧ (N₀ : ℤ) ∣ b)
    (C : AddSubgroup V) (hC : IsAddCyclic C) (hCM : Nat.card C = M')
    (G : Set (V ≃+ V))
    (hG : ∀ a b c d : ℤ, ((N₀ * M' : ℕ) : ℤ) ∣ a * d - b * c - 1 →
      ∃ g ∈ G, g B₁ = a • B₁ + c • B₂ ∧ g B₂ = b • B₁ + d • B₂) :
    2 * (CohCarrier.GammaH (N₀ ^ 2 * M') (ModularCurve.FullLevel.levelH N₀ M') ⊔
        Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      {t : V × V × AddSubgroup V | ∃ g ∈ G, t = (g P₁, g P₂, C.map (g : V →+ V))}.ncard := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_le_ncard_orbit.solution
