import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_Diamond_two_mul_index_gammaH_sup_zpowers_neg_one_le_ncard_orbit_gamma1
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.two_mul_index_gammaH_sup_zpowers_neg_one_le_ncard_orbit_gamma1
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hcop : Nat.Coprime q M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg3 : 3 ≤ ℓg) (hℓgM' : ℓg ∣ M')
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (V : Type) [AddCommGroup V]
    (B₁ B₂ : V) (hB₁ : (q * M') • B₁ = 0) (hB₂ : (q * M') • B₂ = 0)
    (hBi : ∀ a b : ℤ, a • B₁ + b • B₂ = 0 → ((q * M' : ℕ) : ℤ) ∣ a ∧ ((q * M' : ℕ) : ℤ) ∣ b)
    (hBs : ∀ v : V, (q * M') • v = 0 → ∃ a b : ℤ, v = a • B₁ + b • B₂)
    (P₁ P₂ : V) (hP₁ : q • P₁ = 0) (hP₂ : q • P₂ = 0)
    (hPi : ∀ a b : ℤ, a • P₁ + b • P₂ = 0 → (q : ℤ) ∣ a ∧ (q : ℤ) ∣ b)
    (C : AddSubgroup V) (hC : IsAddCyclic C) (hCM : Nat.card C = M')
    (P : V) (hP : ℓg • P = 0) (hP0 : P ≠ 0) (hPC : P ∈ C)
    (G : Set (V ≃+ V))
    (hG : ∀ a b c d : ℤ, ((q * M' : ℕ) : ℤ) ∣ a * d - b * c - 1 →
      ∃ g ∈ G, g B₁ = a • B₁ + c • B₂ ∧ g B₂ = b • B₁ + d • B₂) :
    2 * (CohCarrier.GammaH (q ^ 2 * M') H₁ ⊔
        Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      {t : V × V × AddSubgroup V × V | ∃ g ∈ G, t = (g P₁, g P₂, C.map (g : V →+ V), g P)}.ncard := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_Diamond_two_mul_index_gammaH_sup_zpowers_neg_one_le_ncard_orbit_gamma1.solution
