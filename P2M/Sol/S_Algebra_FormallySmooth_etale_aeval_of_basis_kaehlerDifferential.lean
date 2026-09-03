import Mathlib
import P2M.Util
namespace P2MW.S_Algebra_FormallySmooth_etale_aeval_of_basis_kaehlerDifferential

set_option autoImplicit false

universe u

open KaehlerDifferential

namespace EtaleCoordGC7

open TensorProduct

theorem formallyEtale_of_bijective_mapBaseChange
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Algebra.FormallySmooth R T]
    (h : Function.Bijective (mapBaseChange R S T)) : Algebra.FormallyEtale S T := by

  have hδ : ∀ x : Algebra.H1Cotangent S T, Algebra.H1Cotangent.δ R S T x = 0 := by
    intro x
    apply h.1
    rw [map_zero]
    exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T _).mpr ⟨x, rfl⟩
  haveI : Subsingleton (Algebra.H1Cotangent S T) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x', rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R S T x).mp (hδ x)
    obtain ⟨y', rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R S T y).mp (hδ y)
    rw [Subsingleton.elim x' y']

  haveI : Subsingleton (Ω[T⁄S]) := by
    have hz : ∀ z : Ω[T⁄S], z = 0 := by
      intro z
      obtain ⟨w, rfl⟩ := KaehlerDifferential.map_surjective R S T z
      exact (KaehlerDifferential.exact_mapBaseChange_map R S T w).mpr (h.2 w)
    exact ⟨fun x y => by rw [hz x, hz y]⟩
  exact ⟨inferInstance, inferInstance⟩

end EtaleCoordGC7

open scoped TensorProduct in
open EtaleCoordGC7 in
theorem solution
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Algebra.FormallySmooth R A]
    {ι : Type u} [Finite ι] (a : ι → A)
    (b : Module.Basis ι A (Ω[A⁄R])) (hb : ∀ i, b i = KaehlerDifferential.D R A (a i)) :
    (MvPolynomial.aeval a : MvPolynomial ι R →ₐ[R] A).toRingHom.Etale := by
  classical
  letI algPA : Algebra (MvPolynomial ι R) A := (MvPolynomial.aeval a).toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial ι R) A :=
    IsScalarTower.of_algebraMap_eq fun r => ((MvPolynomial.aeval a).commutes r).symm
  have halg : ∀ p : MvPolynomial ι R, algebraMap (MvPolynomial ι R) A p = MvPolynomial.aeval a p :=
    fun _ => rfl

  let b' : Module.Basis ι A (A ⊗[MvPolynomial ι R] Ω[(MvPolynomial ι R)⁄R]) :=
    Algebra.TensorProduct.basis A (KaehlerDifferential.mvPolynomialBasis R ι)
  have hX : ∀ i, KaehlerDifferential.mvPolynomialBasis R ι i =
      D R (MvPolynomial ι R) (MvPolynomial.X i) :=
    fun i => Module.Basis.apply_eq_iff.mpr (KaehlerDifferential.mvPolynomialBasis_repr_D_X R ι i)
  have hb' : ∀ i, mapBaseChange R (MvPolynomial ι R) A (b' i) = b i := by
    intro i
    rw [Algebra.TensorProduct.basis_apply, mapBaseChange_tmul, one_smul, hX, map_D, halg,
      MvPolynomial.aeval_X, hb]
  have heq : mapBaseChange R (MvPolynomial ι R) A = (b'.equiv b (Equiv.refl ι)).toLinearMap :=
    b'.ext fun i => by rw [hb', LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply, Equiv.refl_apply]
  have hbij : Function.Bijective (mapBaseChange R (MvPolynomial ι R) A) := by
    rw [heq]; exact (b'.equiv b (Equiv.refl ι)).bijective
  haveI : Algebra.FormallyEtale (MvPolynomial ι R) A := formallyEtale_of_bijective_mapBaseChange hbij
  haveI : Algebra.FinitePresentation (MvPolynomial ι R) A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial ι R) A
  haveI : Algebra.Etale (MvPolynomial ι R) A := ⟨inferInstance, inferInstance⟩
  exact RingHom.etale_algebraMap.mpr this
