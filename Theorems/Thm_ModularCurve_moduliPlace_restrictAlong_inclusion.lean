import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_ModularCurve_moduliPlace_restrictAlong_inclusion

set_option autoImplicit false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem ModularCurve.moduliPlace_restrictAlong_inclusion
    (K : Type u) [Field K] [DecidableEq K] (N M : ℕ) [NeZero N] [NeZero M] (hMN : M ∣ N)
    (hex : ∀ x : ModuliPoint N K, ∃ v, IsModuliPlaceOf K N x v)
    (huniq : ∀ (x : ModuliPoint M K) (v v' : Place K ↥(modularFunctionFieldFullC K M)),
      IsModuliPlaceOf K M x v → IsModuliPlaceOf K M x v' → v = v')
    (hι : (IntermediateField.inclusion (full_degeneracyC_le K hMN)).toRingHom.IsIntegral)
    (E : WeierstrassCurve K)
    (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N})
    (C' : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M})
    (hCC' : ∀ T ∈ C.1, (N / M) • T ∈ C'.1) :
    (moduliPlace K N E C.1).restrictAlong
        (IntermediateField.inclusion (full_degeneracyC_le K hMN)) hι =
      moduliPlace K M E C'.1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_moduliPlace_restrictAlong_inclusion.solution
