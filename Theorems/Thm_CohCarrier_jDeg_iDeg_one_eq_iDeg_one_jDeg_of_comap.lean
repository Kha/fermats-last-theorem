import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_jDeg_iDeg_one_eq_iDeg_one_jDeg_of_comap
attribute [-instance] CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.jDeg_iDeg_one_eq_iDeg_one_jDeg_of_comap
    (M M' : ℕ) [NeZero M] [NeZero M'] (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod M')ˣ)
    (d : ℕ) [NeZero d] (h : CohCarrier.LevelLE M M' H H' d) (ht : CohCarrier.LevelLE M M' ⊤ ⊤ d)
    (h₁ : CohCarrier.LevelLE M M ⊤ H 1) (h₁' : CohCarrier.LevelLE M' M' ⊤ H' 1)
    (hH' : ∀ u : (ZMod M')ˣ, u ∈ H' ↔ ZMod.unitsMap h.dvd u ∈ H)
    (A : Type) [AddCommGroup A] (y : CohCarrier.H1 M' ⊤ A) :
    CohCarrier.jDeg M M' H H' d A h (CohCarrier.iDeg' M' M' ⊤ H' 1 A h₁' y) =
      CohCarrier.iDeg' M M ⊤ H 1 A h₁ (CohCarrier.jDeg M M' ⊤ ⊤ d A ht y) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_jDeg_iDeg_one_eq_iDeg_one_jDeg_of_comap.solution
