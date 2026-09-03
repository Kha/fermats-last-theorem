import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import P2M.Util
import P2M.Sol.S_Deformation_wittHomMap_convMul

universe u v w

theorem Deformation.wittHomMap_convMul
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A]
    {B : Type w} [CommRing B] [Bialgebra R B] [Coalgebra.IsCocomm R B]
    (φ ψ : WithConv (B →ₐc[R] A)) (x : Deformation.wittHom R p n B) :
    Deformation.wittHomMap p n (φ * ψ).ofConv x =
      Deformation.wittHomMap p n φ.ofConv x + Deformation.wittHomMap p n ψ.ofConv x := by p2m_exact_reverting @_root_.P2MW.S_Deformation_wittHomMap_convMul.solution
