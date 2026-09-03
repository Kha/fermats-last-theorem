import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_pow_and_reduction_eq_of_mem_closure_endomorphisms_of_forall_isTorsionPoint
attribute [-instance] kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType
attribute [-simp] AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u
set_option maxHeartbeats 800000 in

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isTorsionPoint_pow_and_reduction_eq_of_mem_closure_endomorphisms_of_forall_isTorsionPoint
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (ℓ : ℕ) [Fact ℓ.Prime]
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra A Ω] [IsFractionRing A Ω]
    [Algebra R Ω] [IsScalarTower R A Ω]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (hfin : ∀ k : ℕ, IsFinite (L.schemeNsmul (ℓ ^ k)))
    (htors : ∀ x : SchemeHomOver
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) f,
      ∃ n : ℕ, 0 < n ∧ L.IsTorsionPoint _ n x)
    (S : Set (SchemeHomOver f f))
    (hS : ∀ 𝒯 ∈ S, ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) 𝒯 =
        L.mul t (NeronModelInfra.schemeHomOverComp x 𝒯) (NeronModelInfra.schemeHomOverComp y 𝒯))
    (ext : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f →
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f)
    (hext : ∀ x, Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ (ext x).1 = x.1)
    (k : ℕ)
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f)
    (hy : letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R Ω)));
      y ∈ Subgroup.closure {z | ∃ 𝒯 ∈ S, ∃ x, z = NeronModelInfra.schemeHomOverComp x 𝒯})
    (hred : L.IsTorsionPoint
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A))) (ℓ ^ k)
      (GoodReductionJacobian.schemeHomOverComp
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) rfl (ext y))) :
    ∃ (m : ℕ) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f),
      k ≤ m ∧
      (letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R Ω)));
        z ∈ Subgroup.closure {z | ∃ 𝒯 ∈ S, ∃ x, z = NeronModelInfra.schemeHomOverComp x 𝒯}) ∧
      L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) (ℓ ^ m) z ∧
      GoodReductionJacobian.schemeHomOverComp
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) rfl (ext z) =
        GoodReductionJacobian.schemeHomOverComp
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) rfl (ext y) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_pow_and_reduction_eq_of_mem_closure_endomorphisms_of_forall_isTorsionPoint.solution
