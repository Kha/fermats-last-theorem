import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_CohCarrier_Tower
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import P2M.Util
import P2M.Sol.S_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant

set_option autoImplicit false

open IharaLemma IharaTower

theorem IharaTower.exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {N q : ℕ} [NeZero N] [NeZero q] [NeZero (N * q)] (hq : q.Prime) (hqN : ¬ q ∣ N)
    {H : Subgroup (ZMod N)ˣ} {H' : Subgroup (ZMod (N * q))ˣ}
    (h₁ : CohCarrier.LevelLE N (N * q) H H' 1) (hq' : CohCarrier.LevelLE N (N * q) H H' q)
    {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
    [Module 𝕋 (CohCarrier.H1 N H 𝒪)] [Module 𝕋' (CohCarrier.H1 (N * q) H' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (CohCarrier.H1 N H 𝒪)] [IsScalarTower 𝒪 𝕋' (CohCarrier.H1 (N * q) H' 𝒪)]
    (cd : H1CornerData (𝒪 := 𝒪) N H 𝒪 𝕋) (cd' : H1CornerData (𝒪 := 𝒪) (N * q) H' 𝒪 𝕋')
    (D : DegeneracyDescent (𝒪 := 𝒪) cd cd' 2)
    (hD : D.iRaw = ![CohCarrier.iDegL N (N * q) H H' 1 𝒪 𝒪 h₁, CohCarrier.iDegL N (N * q) H H' q 𝒪 𝒪 hq'])
    (table : Fin 2 → Fin 2 → cd.cornerRing)
    (adjoint_leg : ∀ (k : Fin 2) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B (D.jLeg k m') m = cd'.pairing.B m' (D.iLeg k m))
    (htable : ∀ (k k' : Fin 2) (m : cd.cornerModule), D.jLeg k (D.iLeg k' m) = table k k' • m)
    (c : Fin 2 → cd.cornerRing)
    [Module.Free 𝒪 cd.cornerModule] [Module.Free 𝒪 cd'.cornerModule]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)

    (hc : ∀ v : cd.cornerModule, (∀ k, ∃ w : cd.cornerModule, c k • v = ϖ • w) → ∃ v₁, v = ϖ • v₁)

    (ℓ₀ : ℕ) [NeZero ℓ₀] (hℓ : ℓ₀.Prime) (hℓN : ¬ ℓ₀ ∣ N * q)
    (hne : ∀ v : cd.cornerModule,
      CohCarrier.heckeT N H ℓ₀ 𝒪 (v : CohCarrier.H1 N H 𝒪) - ((ℓ₀ : 𝒪) + 1) • (v : CohCarrier.H1 N H 𝒪)
        ∈ (Ideal.span {ϖ} • ⊤ : Submodule 𝒪 (CohCarrier.H1 N H 𝒪)) → ∃ v₁ : cd.cornerModule, v = ϖ • v₁)

    (hihara : ∀ g h : CohCarrier.H1 N H (𝒪 ⧸ Ideal.span {ϖ}),
      (∀ σ : CongruenceSubgroup.Gamma0 N, CohCarrier.diamondRaw N H (𝒪 ⧸ Ideal.span {ϖ}) σ g = g) →
      (∀ σ : CongruenceSubgroup.Gamma0 N, CohCarrier.diamondRaw N H (𝒪 ⧸ Ideal.span {ϖ}) σ h = h) →
      CohCarrier.iDeg' N (N * q) H H' 1 (𝒪 ⧸ Ideal.span {ϖ}) h₁ g +
          CohCarrier.iDeg' N (N * q) H H' q (𝒪 ⧸ Ideal.span {ϖ}) hq' h = 0 →
        CohCarrier.IsEis 𝒪 (𝒪 ⧸ Ideal.span {ϖ}) N H ℓ₀ g ∧ CohCarrier.IsEis 𝒪 (𝒪 ⧸ Ideal.span {ϖ}) N H ℓ₀ h)

    (hdia : ∀ (σ : CongruenceSubgroup.Gamma0 N) (v : cd.cornerModule),
      CohCarrier.diamondRaw N H 𝒪 σ (v : CohCarrier.H1 N H 𝒪) = (v : CohCarrier.H1 N H 𝒪)) :
    ∀ (v : cd.cornerModule) (x : cd'.cornerModule),
      RungAssembly.iComb (D.toLegDatum table adjoint_leg htable) c v = ϖ • x → ∃ v₁, v = ϖ • v₁ := by p2m_exact_reverting @_root_.P2MW.S_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant.solution
