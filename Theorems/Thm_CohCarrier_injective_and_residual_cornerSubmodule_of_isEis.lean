import Definitions.Def_CohCarrier_Tower
import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import P2M.Util
import P2M.Sol.S_CohCarrier_injective_and_residual_cornerSubmodule_of_isEis
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

theorem CohCarrier.injective_and_residual_cornerSubmodule_of_isEis
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (N q : ℕ) [NeZero q] (hqu : IsUnit (q : 𝒪))
    (h₁ : CohCarrier.LevelLE N (N * q) ⊤ ⊤ 1) (hq : CohCarrier.LevelLE N (N * q) ⊤ ⊤ q)
    (h₁' : CohCarrier.LevelLE (N * q) (N * q * q) ⊤ ⊤ 1)
    (hq' : CohCarrier.LevelLE (N * q) (N * q * q) ⊤ ⊤ q)

    (ℓ₀ : ℕ) [NeZero ℓ₀] (hℓ₀ : ℓ₀.Prime) (hℓ₀N : ¬ ℓ₀ ∣ N) (hℓ₀q : ¬ ℓ₀ ∣ q)

    (hihara : ∀ (A : Type) [AddCommGroup A] [Module 𝒪 A],
      (∀ a : A, (q : ℤ) • a = 0 → a = 0) →
      (∀ g h : CohCarrier.H1 N ⊤ A,
          CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 A h₁ g + CohCarrier.iDeg' N (N * q) ⊤ ⊤ q A hq h = 0 →
            CohCarrier.IsEis 𝒪 A N ⊤ ℓ₀ g ∧ CohCarrier.IsEis 𝒪 A N ⊤ ℓ₀ h) ∧
      (∀ x z' : CohCarrier.H1 (N * q) ⊤ A,
          CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' x +
              CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' z' = 0 →
            ∃ w : CohCarrier.H1 N ⊤ A,
              CohCarrier.IsEis 𝒪 A (N * q) ⊤ ℓ₀ (z' - CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 A h₁ w) ∧
                CohCarrier.IsEis 𝒪 A (N * q) ⊤ ℓ₀ (x + CohCarrier.iDeg' N (N * q) ⊤ ⊤ q A hq w)))

    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (CohCarrier.H1 N ⊤ 𝒪)]
    [IsScalarTower 𝒪 𝕋 (CohCarrier.H1 N ⊤ 𝒪)]
    (Sp : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin Sp.n)
    (tℓ : 𝕋) (htℓ : ∀ v : CohCarrier.H1 N ⊤ 𝒪, tℓ • v = CohCarrier.heckeT N ⊤ ℓ₀ 𝒪 v)
    (hEis : tℓ - ((ℓ₀ : 𝕋) + 1) ∉ Sp.𝔪 i₀) :
    (∀ v : CohCarrier.H1 N ⊤ 𝒪,
        v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) →
        q • CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 𝒪 h₁'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h₁ v)
            - CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q 𝒪 hq'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h₁ (CohCarrier.heckeT N ⊤ q 𝒪 v))
            + CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q 𝒪 hq'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ q 𝒪 hq v) = 0 →
        v = 0) ∧
    (∀ v : CohCarrier.H1 N ⊤ 𝒪,
        v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) →
        ∀ x : CohCarrier.H1 (N * q * q) ⊤ 𝒪,
        q • CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 𝒪 h₁'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h₁ v)
            - CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q 𝒪 hq'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h₁ (CohCarrier.heckeT N ⊤ q 𝒪 v))
            + CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q 𝒪 hq'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ q 𝒪 hq v) = ϖ • x →
        ∃ v₁ : CohCarrier.H1 N ⊤ 𝒪,
          v₁ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) ∧ v = ϖ • v₁) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_injective_and_residual_cornerSubmodule_of_isEis.solution
