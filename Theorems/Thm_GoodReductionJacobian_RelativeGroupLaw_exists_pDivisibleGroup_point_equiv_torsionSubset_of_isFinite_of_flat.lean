import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat
attribute [-simp] GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat
    {R : Type} [CommRing R] [IsLocalRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (p h : ℕ)
    (hfin : ∀ v : ℕ, IsFinite (L.schemeNsmul (p ^ v)))
    (hflat : ∀ v : ℕ, Flat (L.schemeNsmul (p ^ v)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra R Ω]
    (hcard : ∀ v : ℕ,
      Nat.card (L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) (p ^ v)) =
        p ^ (v * h)) :
    ∃ (G : PDivisibleGroup R p h)
      (e : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T],
        G.Point T v ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v)),
      (∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x y : G.Point T v),
        ((e v T (x * y)).val : SchemeHomOver _ f) = L.mul _ (e v T x).val (e v T y).val) ∧
      (∀ (v : ℕ) (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
        (a : T →ₐ[R] T') (x : G.Point T v),
        ((e v T' (G.pointMap a v x)).val : SchemeHomOver _ f).1 =
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e v T x).val.1) ∧
      (∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x : G.Point T v),
        ((e (v + 1) T (G.pointIncl T v x)).val : SchemeHomOver _ f) = (e v T x).val) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat.solution
