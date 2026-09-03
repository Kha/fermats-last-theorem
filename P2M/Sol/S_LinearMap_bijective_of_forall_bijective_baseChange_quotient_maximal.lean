import Mathlib
import P2M.Util
namespace P2MW.S_LinearMap_bijective_of_forall_bijective_baseChange_quotient_maximal

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N)
    (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], Function.Bijective (f.baseChange (R ⧸ 𝔪))) :
    Function.Bijective f := by
  classical

  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : Subsingleton M := Module.subsingleton R M
    haveI : Subsingleton N := Module.subsingleton R N
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

  let bM := Module.Free.chooseBasis R M
  let bN := Module.Free.chooseBasis R N
  obtain ⟨𝔪₀, h𝔪₀⟩ := Ideal.exists_maximal R
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R M) = Fintype.card (Module.Free.ChooseBasisIndex R N) := by
    haveI := h𝔪₀
    let e := LinearEquiv.ofBijective (f.baseChange (R ⧸ 𝔪₀)) (h 𝔪₀)
    have h1 := e.finrank_eq
    rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (R ⧸ 𝔪₀) bM),
      Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (R ⧸ 𝔪₀) bN)] at h1
    exact h1
  let σ : Module.Free.ChooseBasisIndex R N ≃ Module.Free.ChooseBasisIndex R M := (Fintype.equivOfCardEq hcard).symm
  let bN' : Module.Basis (Module.Free.ChooseBasisIndex R M) R N := bN.reindex σ

  let A := LinearMap.toMatrix bM bN' f
  suffices hdet : IsUnit A.det by
    exact (LinearEquiv.ofIsUnitDet hdet).bijective

  by_contra hndet
  obtain ⟨𝔪, h𝔪, hmem⟩ := exists_max_ideal_of_mem_nonunits hndet
  haveI := h𝔪
  have hzero : (A.map (algebraMap R (R ⧸ 𝔪))).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hA : LinearMap.toMatrix (Algebra.TensorProduct.basis (R ⧸ 𝔪) bM) (Algebra.TensorProduct.basis (R ⧸ 𝔪) bN')
      (f.baseChange (R ⧸ 𝔪)) = A.map (algebraMap R (R ⧸ 𝔪)) := LinearMap.toMatrix_baseChange _ _ _ _
  have hunit : IsUnit (LinearMap.toMatrix (Algebra.TensorProduct.basis (R ⧸ 𝔪) bM) (Algebra.TensorProduct.basis (R ⧸ 𝔪) bN')
      (f.baseChange (R ⧸ 𝔪))).det := by
    have := LinearEquiv.isUnit_det (LinearEquiv.ofBijective (f.baseChange (R ⧸ 𝔪)) (h 𝔪))
      (Algebra.TensorProduct.basis (R ⧸ 𝔪) bM) (Algebra.TensorProduct.basis (R ⧸ 𝔪) bN')
    exact this
  rw [hA, hzero] at hunit
  exact not_isUnit_zero hunit
