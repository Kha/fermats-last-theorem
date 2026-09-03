import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import P2M.Util
namespace P2MW.S_Deformation_wittHomMap_convMul

set_option autoImplicit false

open Function Deformation Deformation.TruncWitt

universe u v w

theorem solution
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A]
    {B : Type w} [CommRing B] [Bialgebra R B] [Coalgebra.IsCocomm R B]
    (φ ψ : WithConv (B →ₐc[R] A)) (x : Deformation.wittHom R p n B) :
    Deformation.wittHomMap p n (φ * ψ).ofConv x =
      Deformation.wittHomMap p n φ.ofConv x + Deformation.wittHomMap p n ψ.ofConv x := by
  refine Subtype.ext ?_
  rw [AddSubgroup.coe_add, coe_wittHomMap, coe_wittHomMap, coe_wittHomMap]
  have h := map_convMul_of_mem_wittHom (T := A) x.2
    (WithConv.toConv (φ.ofConv : B →ₐ[R] A)) (WithConv.toConv (ψ.ofConv : B →ₐ[R] A))
  have hmul : ((φ * ψ).ofConv : B →ₐ[R] A) =
      (WithConv.toConv (φ.ofConv : B →ₐ[R] A) * WithConv.toConv (ψ.ofConv : B →ₐ[R] A)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul φ ψ)
  rw [hmul]
  exact h
