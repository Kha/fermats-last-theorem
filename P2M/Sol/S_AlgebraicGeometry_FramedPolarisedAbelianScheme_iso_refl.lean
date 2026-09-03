import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_refl

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S) :
    FramedPolarisedAbelianScheme.Iso X X := by
  refine ⟨Iso.refl X.A, by rw [Iso.refl_hom, Category.id_comp], ?_, ?_, ?_, ?_⟩
  · rw [Iso.refl_hom, Category.id_comp]
  · intro T t x y
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    simp only [Iso.refl_hom, Category.comp_id]
  · intro i
    rw [Iso.refl_hom, Category.comp_id]
  · intro s
    refine ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (X.f ⁻¹ᵁ ⊤).ι).mapIso ?_⟩⟩
    rw [Iso.refl_hom]
    exact (Scheme.Modules.pullbackId X.A).app X.pol
