import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import P2M.Util
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_specMap_comp_eq_of_injective

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T K : Type u} [CommRing T] [IsReduced T] [CommRing K] (f : T →+* K) (hf : Function.Injective f)
    (W : WeierstrassCurve T) (P P' : Section W)
    (h : Spec.map (CommRingCat.ofHom f) ≫ P.1 = Spec.map (CommRingCat.ofHom f) ≫ P'.1) :
    P = P' := by
  haveI : IsSeparated (projModelStrCR W.toProjective) := by unfold projModelStrCR; infer_instance
  haveI : IsDominant (Spec.map (CommRingCat.ofHom f)) := by
    refine ⟨?_⟩
    show DenseRange (PrimeSpectrum.comap f)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot f).mp hf]
    exact bot_le
  apply Subtype.ext
  exact ext_of_isDominant_of_isSeparated (projModelStrCR W.toProjective) (by rw [P.2, P'.2])
    (Spec.map (CommRingCat.ofHom f)) h
