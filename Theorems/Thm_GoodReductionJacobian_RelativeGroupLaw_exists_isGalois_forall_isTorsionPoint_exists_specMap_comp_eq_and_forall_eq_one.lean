import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one
attribute [-instance] kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one
    (K : Type u) [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (G : RelativeGroupLaw K f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (hA : AbelianSchemePropertyBundle K f) (d : ℕ) [SmoothOfRelativeDimension d f]
    (n : ℕ) (hn : (n : K) ≠ 0)
    (Ω : Type u) [Field Ω] [Algebra K Ω] [Normal K Ω] :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      (∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f,
        G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) n x →
        ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) f,
          G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z ∧
          Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ z.1 = x.1) ∧
      (∀ τ : L ≃ₐ[K] L,
        (∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) f,
          G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z →
          Spec.map (CommRingCat.ofHom (τ : L →+* L)) ≫ z.1 = z.1) → τ = 1) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one.solution
