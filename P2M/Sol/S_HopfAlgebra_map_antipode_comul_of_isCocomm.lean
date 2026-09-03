import Mathlib
import Theorems.Thm_HopfAlgebra_comul_antipode
import P2M.Util
namespace P2MW.S_HopfAlgebra_map_antipode_comul_of_isCocomm

open scoped TensorProduct
open Coalgebra HopfAlgebra

theorem solution {R : Type*} [CommSemiring R]
    {A : Type*} [Semiring A] [HopfAlgebra R A] (hcocomm : Coalgebra.IsCocomm R A) (a : A) :
    TensorProduct.map (antipode R) (antipode R) (comul a)
      = comul (antipode R a) := by
  haveI := hcocomm
  have h := HopfAlgebra.comul_antipode (R := R) a
  rw [h]
  have hτS : ∀ z : A ⊗[R] A,
      TensorProduct.comm R A A (TensorProduct.map (antipode R) (antipode R) z)
        = TensorProduct.map (antipode R) (antipode R) (TensorProduct.comm R A A z) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y => simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
    | add z₁ z₂ h₁ h₂ => simp [map_add, h₁, h₂]
  rw [hτS]

  congr 1

  first
    | exact (Coalgebra.IsCocomm.comm_comul (R := R) a).symm
    | exact (Coalgebra.comm_comul (R := R) a).symm
    | exact (Coalgebra.IsCocomm.comul_comm (R := R) a)
    | exact (Coalgebra.comul_comm (R := R) a)
    | simp only [Coalgebra.IsCocomm.comm_comp_comul]
    | exact (LinearMap.congr_fun (Coalgebra.IsCocomm.comm_comp_comul (R := R) (A := A)) a).symm
    | exact (LinearMap.congr_fun hcocomm.comm_comp_comul a).symm
    | rfl
