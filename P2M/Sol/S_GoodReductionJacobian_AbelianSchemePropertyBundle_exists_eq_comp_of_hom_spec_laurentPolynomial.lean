import Mathlib
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_exists_toLaurent_comp_eq_of_isProper
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_polynomial
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_laurentPolynomial

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    (hA : AbelianSchemePropertyBundle k f)
    (φ : Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ A)
    (hφ : φ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))) :
    ∃ a : Spec (CommRingCat.of k) ⟶ A, a ≫ f = 𝟙 _ ∧
      φ = Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))) ≫ a := by
  haveI := hA.proper

  obtain ⟨ψ, hψ, hψf⟩ := AlgebraicGeometry.exists_toLaurent_comp_eq_of_isProper f φ hφ

  obtain ⟨a, ha, h0⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_polynomial hA ψ hψf
  refine ⟨a, ha, ?_⟩
  rw [← hψ, h0, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  exact RingHom.ext fun x => by
    rw [RingHom.comp_apply, Polynomial.algebraMap_eq, Polynomial.toLaurent_C,
      LaurentPolynomial.C_eq_algebraMap]
