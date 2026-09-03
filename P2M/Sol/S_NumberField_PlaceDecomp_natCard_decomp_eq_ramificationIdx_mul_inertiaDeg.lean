import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import P2M.Util
namespace P2MW.S_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open CategoryTheory IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

set_option maxHeartbeats 800000

open NumberField.PlaceDecomp in
open scoped Pointwise NumberField.PlaceTransport in
theorem solution
    (K K'' : Type) [Field K] [NumberField K] [Field K''] [NumberField K''] [Algebra K K''] [IsGalois K K'']
    (w'' : HeightOneSpectrum (𝓞 K'')) :
    Nat.card (decomp K K'' w'') =
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w'').asIdeal w''.asIdeal *
        Ideal.inertiaDeg' (HeightOneSpectrum.under (𝓞 K) w'').asIdeal w''.asIdeal := by
  classical
  let G := K'' ≃ₐ[K] K''
  let P : Ideal (𝓞 K'') := w''.asIdeal
  let p : Ideal (𝓞 K) := (HeightOneSpectrum.under (𝓞 K) w'').asIdeal
  haveI : P.IsMaximal := w''.isMaximal
  haveI : P.LiesOver p := ⟨rfl⟩
  have hp : p ≠ ⊥ := (HeightOneSpectrum.under (𝓞 K) w'').ne_bot
  haveI : p.IsMaximal := (HeightOneSpectrum.under (𝓞 K) w'').isMaximal
  letI := Ideal.Quotient.field p
  letI := Ideal.Quotient.field P
  haveI : Finite ((𝓞 K) ⧸ p) := inferInstance
  haveI : PerfectField ((𝓞 K) ⧸ p) := PerfectField.ofFinite
  haveI : Module.Finite ((𝓞 K) ⧸ p) ((𝓞 K'') ⧸ P) := inferInstance
  haveI : Algebra.IsSeparable ((𝓞 K) ⧸ p) ((𝓞 K'') ⧸ P) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField (K := (𝓞 K) ⧸ p) (L := (𝓞 K'') ⧸ P)
  have h1 : Nat.card (MulAction.stabilizer G P) = p.ramificationIdx' P * p.inertiaDeg' P := by
    rw [Ideal.card_stabilizer_eq (G := G) p P, Ideal.ramificationIdxIn_eq_ramificationIdx p P G,
      Ideal.inertiaDegIn_eq_inertiaDeg p P G, ← Ideal.ramificationIdx'_eq_ramificationIdx p P hp,
      ← Ideal.inertiaDeg'_eq_inertiaDeg p P]
  have h2 : (decomp K K'' w'' : Subgroup G) = MulAction.stabilizer G P := by
    rw [← NumberField.PlaceTransport.stabilizer_eq_decomp K K'' w'']
    ext σ
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, HeightOneSpectrum.ext_iff,
      NumberField.PlaceTransport.smul_asIdeal_eq_map, Ideal.pointwise_smul_def]
    rfl
  rw [h2]
  exact h1
