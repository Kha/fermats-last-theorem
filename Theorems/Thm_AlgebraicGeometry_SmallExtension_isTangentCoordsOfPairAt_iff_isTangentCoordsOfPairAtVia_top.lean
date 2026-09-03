import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_iff_isTangentCoordsOfPairAtVia_top

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension

universe u

theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_iff_isTangentCoordsOfPairAtVia_top
    {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C]
    {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))) :
    IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c ↔
      IsTangentCoordsOfPairAtVia I V ι C u v xk Lk ⊤ ((⊤ : Ak.Opens).ι ≫ ak) Ue c := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_iff_isTangentCoordsOfPairAtVia_top.solution
