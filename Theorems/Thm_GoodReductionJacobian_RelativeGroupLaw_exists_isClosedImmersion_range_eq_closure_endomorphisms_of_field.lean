import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_range_eq_closure_endomorphisms_of_field
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u
set_option maxHeartbeats 800000 in

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_range_eq_closure_endomorphisms_of_field
    {k : Type u} [Field k]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    (hJ : AbelianSchemePropertyBundle k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (S : Set (SchemeHomOver f f))
    (hS : ∀ 𝒯 ∈ S, ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) 𝒯 =
        L.mul t (NeronModelInfra.schemeHomOverComp x 𝒯) (NeronModelInfra.schemeHomOverComp y 𝒯)) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of k)) (LB : RelativeGroupLaw k g)
      (i : SchemeHomOver g f),
      AbelianSchemePropertyBundle k g ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
        LB.mul t x y = LB.mul t y x) ∧
      IsClosedImmersion i.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp (LB.mul t x y) i =
          L.mul t (NeronModelInfra.schemeHomOverComp x i) (NeronModelInfra.schemeHomOverComp y i)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω],
        letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap k Ω)));
        ∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f,
          (∃ b : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) g,
              NeronModelInfra.schemeHomOverComp b i = z) ↔
            z ∈ Subgroup.closure {z | ∃ 𝒯 ∈ S, ∃ x, z = NeronModelInfra.schemeHomOverComp x 𝒯}) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_range_eq_closure_endomorphisms_of_field.solution
