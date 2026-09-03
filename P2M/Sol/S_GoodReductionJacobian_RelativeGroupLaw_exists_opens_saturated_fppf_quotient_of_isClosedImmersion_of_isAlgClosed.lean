import Mathlib
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_affine_etale_slice_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_sliceQuotient
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_isClosedImmersion_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) :
    ∃ (U : G.Opens) (hU : CategoryTheory.Limits.pullback.snd (i ≫ f) f ⁻¹ᵁ U = L.action i ⁻¹ᵁ U),
      Nonempty (U.toScheme) ∧
      ∃ (Y : Scheme.{u}) (p : (U).toScheme ⟶ Y),
        (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U) ≫ p =
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) ≫ p ∧
        Flat p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ Surjective p ∧
        IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U)
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) p p := by
  obtain ⟨S, j, hSaff, hSne, hSsm, hEt⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_affine_etale_slice_of_isAlgClosed k f L g i LN h hi
  haveI := hSaff; haveI := hSne; haveI := hSsm
  haveI : Smooth (j ≫ f) := SmoothOfRelativeDimension.smooth (g - h) (j ≫ f)
  haveI : LocallyOfFiniteType (j ≫ f) := inferInstance
  obtain ⟨V, hV, hVne, hf1, hfl1, hlfp1, hf2, hfl2, hlfp2, hmono, hequiv, haff⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale
      k f L g i LN h hi S j hEt
  haveI := hVne; haveI := hf1; haveI := hfl1; haveI := hlfp1; haveI := hf2; haveI := hfl2; haveI := hlfp2
  obtain ⟨Y, π, w, hπf, hπfl, hπlfp, hπsurj, hRπ, ⟨hcoeq⟩⟩ :=
    AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation _ _ hmono hequiv haff
  haveI := hπf; haveI := hπfl; haveI := hπlfp; haveI := hπsurj
  exact GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_fppf_quotient_of_sliceQuotient
    k f L g i LN h hi S j hEt V hV π w hRπ hcoeq
