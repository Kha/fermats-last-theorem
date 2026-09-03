import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_relIndex_finiteIdeleStabilizer_inf_map_conj_eq_local
attribute [-simp] QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star CerednikDrinfeld.HeckeData.mk.sizeOf_spec CerednikDrinfeld.Matching.mk.injEq CerednikDrinfeld.DegeneracyData.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.mk.injEq CerednikDrinfeld.ribbonGram_apply CerednikDrinfeld.HeckeData.mk.injEq CerednikDrinfeld.Matching.mk.sizeOf_spec ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra

theorem QuaternionAlgebra.IsOrder.relIndex_finiteIdeleStabilizer_inf_map_conj_eq_local
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      ∀ u ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ
          ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) :
            Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)),
        (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom s)⁻¹ * u *
            Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom s ∈
          MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ
            ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) :
              Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ))) :
    (Submodule.finiteIdeleStabilizer Λ ⊓
        (Submodule.finiteIdeleStabilizer Λ).map (MulAut.conj s).toMonoidHom).relIndex
      (Submodule.finiteIdeleStabilizer Λ) =
    (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ
          ((Submodule.localBox Λ v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) :
            Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) ⊓
        (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ
          ((Submodule.localBox Λ v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) :
            Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))).map
          (MulAut.conj (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom s)).toMonoidHom).relIndex
      (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ
          ((Submodule.localBox Λ v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) :
            Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_relIndex_finiteIdeleStabilizer_inf_map_conj_eq_local.solution
