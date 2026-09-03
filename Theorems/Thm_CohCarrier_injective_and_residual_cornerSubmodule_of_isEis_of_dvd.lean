import Definitions.Def_CohCarrier_Tower
import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import P2M.Util
import P2M.Sol.S_CohCarrier_injective_and_residual_cornerSubmodule_of_isEis_of_dvd
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

theorem CohCarrier.injective_and_residual_cornerSubmodule_of_isEis_of_dvd
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (N q : ℕ) [NeZero N] [NeZero q] (hqu : IsUnit (q : 𝒪))
    (h₁ : CohCarrier.LevelLE N (N * q) ⊤ ⊤ 1) (hq : CohCarrier.LevelLE N (N * q) ⊤ ⊤ q)
    (h₁' : CohCarrier.LevelLE (N * q) (N * q * q) ⊤ ⊤ 1)
    (hq' : CohCarrier.LevelLE (N * q) (N * q * q) ⊤ ⊤ q)

    (L L' : ℕ) (hL : L = N * q) (hL' : L' = L * q)
    (k₁ : CohCarrier.LevelLE L L' ⊤ ⊤ 1) (kq : CohCarrier.LevelLE L L' ⊤ ⊤ q)

    (ℓ₀ : ℕ) [NeZero ℓ₀] (hℓ₀ : ℓ₀.Prime)

    (hihara : ∀ (A : Type) [AddCommGroup A] [Module 𝒪 A],
      (∀ a : A, (q : ℤ) • a = 0 → a = 0) →
      ∀ x z' : CohCarrier.H1 (N * q) ⊤ A,
        CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' x +
            CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' z' = 0 →
          ∃ w : CohCarrier.H1 N ⊤ A,
            CohCarrier.IsEis 𝒪 A (N * q) ⊤ ℓ₀ (z' - CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 A h₁ w) ∧
              CohCarrier.IsEis 𝒪 A (N * q) ⊤ ℓ₀ (x + CohCarrier.iDeg' N (N * q) ⊤ ⊤ q A hq w))

    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (CohCarrier.H1 L ⊤ 𝒪)]
    [IsScalarTower 𝒪 𝕋 (CohCarrier.H1 L ⊤ 𝒪)]
    (Sp : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin Sp.n)
    (tℓ : 𝕋) (htℓ : ∀ v : CohCarrier.H1 L ⊤ 𝒪, tℓ • v = CohCarrier.heckeT L ⊤ ℓ₀ 𝒪 v)
    (hEis : tℓ - ((ℓ₀ : 𝕋) + 1) ∉ Sp.𝔪 i₀)

    (G : Set ℕ) (hG : ∀ ℓ ∈ G, ℓ.Prime ∧ ¬ ℓ ∣ N * q)
    (tT : ∀ ℓ : ℕ, ℓ ∈ G → 𝕋) (c : ∀ ℓ : ℕ, ℓ ∈ G → 𝒪)
    (htT : ∀ (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ ∈ G) (v : CohCarrier.H1 L ⊤ 𝒪),
      tT ℓ hℓ • v = CohCarrier.heckeT L ⊤ ℓ 𝒪 v)
    (hc : ∀ (ℓ : ℕ) (hℓ : ℓ ∈ G), tT ℓ hℓ - algebraMap 𝒪 𝕋 (c ℓ hℓ) ∈ Sp.𝔪 i₀)
    (hnew : ∀ v : CohCarrier.H1 N ⊤ (IsLocalRing.ResidueField 𝒪),
      (∀ (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ ∈ G),
        CohCarrier.heckeT N ⊤ ℓ (IsLocalRing.ResidueField 𝒪) v =
          IsLocalRing.residue 𝒪 (c ℓ hℓ) • v) →
      v = 0) :
    (∀ v : CohCarrier.H1 L ⊤ 𝒪,
        v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀) →
        CohCarrier.iDeg' L L' ⊤ ⊤ q 𝒪 kq (CohCarrier.heckeT L ⊤ q 𝒪 v)
            - q • CohCarrier.iDeg' L L' ⊤ ⊤ 1 𝒪 k₁ v = 0 →
        v = 0) ∧
    (∀ v : CohCarrier.H1 L ⊤ 𝒪,
        v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀) →
        ∀ x : CohCarrier.H1 L' ⊤ 𝒪,
        CohCarrier.iDeg' L L' ⊤ ⊤ q 𝒪 kq (CohCarrier.heckeT L ⊤ q 𝒪 v)
            - q • CohCarrier.iDeg' L L' ⊤ ⊤ 1 𝒪 k₁ v = ϖ • x →
        ∃ v₁ : CohCarrier.H1 L ⊤ 𝒪,
          v₁ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀) ∧ v = ϖ • v₁) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_injective_and_residual_cornerSubmodule_of_isEis_of_dvd.solution
