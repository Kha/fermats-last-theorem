import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_CohCarrier_isEigensystemH1_one_of_heckeT_eq_smul
attribute [-instance] CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq

set_option autoImplicit false

theorem CohCarrier.isEigensystemH1_one_of_heckeT_eq_smul
    (N : ℕ) {K : Type} [Field K] (S₀ : Set ℕ) (lam : ℕ → K)
    (v : CohCarrier.H1 N ⊤ K) (hv : v ≠ 0)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT N ⊤ ℓ K v) = lam ℓ • v) :
    HeckeEis.IsEigensystemH1 N (1 : Representation K (CongruenceSubgroup.Gamma0 N) K)
      (fun _ => LinearMap.id) S₀ lam := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_isEigensystemH1_one_of_heckeT_eq_smul.solution
