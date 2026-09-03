import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_HeckeModule_IharaRungDatum
import P2M.Util
import P2M.Sol.S_IharaTower_exists_levelPairing_cornerSubmodule_of_stable_of_selfAdjoint
attribute [-instance] CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

set_option autoImplicit false

p2m_open "IharaLemma IharaTower~exists_levelPairing_cornerSubmodule_of_le"

theorem IharaTower.exists_levelPairing_cornerSubmodule_of_stable_of_selfAdjoint
    {𝒪 : Type} [CommRing 𝒪] {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
    (W₀ : Submodule 𝒪 V) (hstab : ∀ (t : 𝕋) (w : V), w ∈ W₀ → t • w ∈ W₀)
    (B : W₀ →ₗ[𝒪] W₀ →ₗ[𝒪] 𝒪) (hB : Function.Bijective B)
    (hadj : ∀ (t : 𝕋) (x y Tx Ty : W₀), (Tx : V) = t • (x : V) → (Ty : V) = t • (y : V) →
      B Tx y = B x Ty)
    (S : IdempotentSplitting 𝕋) (i : Fin S.n)
    (hle : ∀ v : V, v ∈ cornerSubmodule (M := V) (S.e i) → v ∈ W₀) :
    ∃ P : LevelPairing (𝒪 := 𝒪) (S.CornerRing i) ↥(cornerSubmodule (M := V) (S.e i)),
      ∀ x y : ↥(cornerSubmodule (M := V) (S.e i)),
        P.B x y = B ⟨(x : V), hle _ x.2⟩ ⟨(y : V), hle _ y.2⟩ := by p2m_exact_reverting @_root_.P2MW.S_IharaTower_exists_levelPairing_cornerSubmodule_of_stable_of_selfAdjoint.solution
