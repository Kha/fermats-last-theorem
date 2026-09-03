import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_mvPolynomial_aeval_eq_zero_and_aeval_notMem_of_forall_eq_zero
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open IsLocalRing
open scoped IsMulCommutative

theorem CohCarrier.exists_mvPolynomial_aeval_eq_zero_and_aeval_notMem_of_forall_eq_zero
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (M : ℕ) [NeZero M] (S : Set ℕ)
    (hcomm : ∀ g g' : CohCarrier.Gen M S,
      CohCarrier.opFamily M ⊤ S 𝒪 g * CohCarrier.opFamily M ⊤ S 𝒪 g' =
        CohCarrier.opFamily M ⊤ S 𝒪 g' * CohCarrier.opFamily M ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen M S → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata M ⊤ S 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)

    {ι : Type} (ℓ : ι → ℕ) (hℓ : ∀ i : ι, (ℓ i).Prime) (hℓS : ∀ i : ι, ℓ i ∉ S)
    (hℓM : ∀ i : ι, ¬ ℓ i ∣ M) (c : ι → ResidueField 𝒪)
    (hnew : ∀ v : CohCarrier.H1 M ⊤ (ResidueField 𝒪),
      (∀ i : ι, (haveI : NeZero (ℓ i) := ⟨(hℓ i).ne_zero⟩;
        CohCarrier.heckeT M ⊤ (ℓ i) (ResidueField 𝒪) v) = c i • v) →
      v = 0)
    (i₀ : Fin Sp.n) :
    ∃ f : MvPolynomial ι 𝒪,
      MvPolynomial.aeval (R := 𝒪) c f = 0 ∧
      MvPolynomial.aeval (R := 𝒪)
          (fun i : ι => (⟨(CohCarrier.hdata M ⊤ S 𝒪 (ResidueField 𝒪) hcomm θbar).op
              (CohCarrier.Gen.T (ℓ i) (hℓ i) (hℓS i) (hℓM i)),
            Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
            ↥(CohCarrier.hdata M ⊤ S 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)) f
        ∉ Sp.𝔪 i₀ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_mvPolynomial_aeval_eq_zero_and_aeval_notMem_of_forall_eq_zero.solution
