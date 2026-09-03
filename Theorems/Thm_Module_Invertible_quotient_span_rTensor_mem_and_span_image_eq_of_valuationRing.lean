import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Invertible_quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem Module.Invertible.quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing
    {𝒪 : Type u} [CommRing 𝒪]
    (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra 𝒪 V]
    (L : Type v) [Field L] [Algebra 𝒪 L] [Algebra V L] [IsScalarTower 𝒪 V L] [IsFractionRing V L]
    (M : Type w) [AddCommGroup M] [Module 𝒪 M] [Module.Finite 𝒪 M]
    (N : Submodule L (L ⊗[𝒪] M)) (hN : Module.Invertible L ((L ⊗[𝒪] M) ⧸ N)) :
    Module.Invertible V ((V ⊗[𝒪] M) ⧸ Submodule.span V
        {x : V ⊗[𝒪] M | LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ N}) ∧
      Submodule.span L (LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap ''
        (Submodule.span V {x : V ⊗[𝒪] M | LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ N} :
          Set (V ⊗[𝒪] M))) = N := by p2m_exact_reverting @_root_.P2MW.S_Module_Invertible_quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing.solution
