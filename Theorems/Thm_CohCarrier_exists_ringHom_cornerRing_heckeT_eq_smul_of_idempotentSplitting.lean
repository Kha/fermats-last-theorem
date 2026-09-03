import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_ringHom_cornerRing_heckeT_eq_smul_of_idempotentSplitting

set_option autoImplicit false

open IsLocalRing
open scoped IsMulCommutative
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem CohCarrier.exists_ringHom_cornerRing_heckeT_eq_smul_of_idempotentSplitting
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (L : ℕ) [NeZero L] (S : Set ℕ)
    (hcomm : ∀ g h : CohCarrier.Gen L S,
      CohCarrier.opFamily L ⊤ S 𝒪 g * CohCarrier.opFamily L ⊤ S 𝒪 h =
        CohCarrier.opFamily L ⊤ S 𝒪 h * CohCarrier.opFamily L ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen L S → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata L ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (K : Type) [Field K] [IsAlgClosed K] [Algebra 𝒪 K]
    (hinj : Function.Injective (algebraMap 𝒪 K)) :
    ∃ (φ : Sp.CornerRing i₀ →+* K) (c : CohCarrier.H1 L ⊤ K), c ≠ 0 ∧
      ((∀ v : CohCarrier.H1 L ⊤ 𝒪,
          v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀) →
            v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH L ⊤) 𝒪) →
        c ∈ ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH L ⊤) K) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT L ⊤ ℓ K c) =
          φ (Sp.toCornerRing i₀
            ⟨(CohCarrier.hdata L ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op (CohCarrier.Gen.T ℓ hℓ hℓS hℓL),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩) • c) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L),
        (haveI : NeZero q := ⟨hq.ne_zero⟩; CohCarrier.heckeT L ⊤ q K c) =
          φ (Sp.toCornerRing i₀
            ⟨(CohCarrier.hdata L ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op (CohCarrier.Gen.U q hq hqL),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩) • c) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_ringHom_cornerRing_heckeT_eq_smul_of_idempotentSplitting.solution
