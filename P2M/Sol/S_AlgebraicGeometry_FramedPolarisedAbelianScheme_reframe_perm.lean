import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isReframe
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_reframe_perm
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S) (π : Fin (N + 1) ≃ Fin (N + 1)) :
    ∃ F' : Scheme.Modules.ProjPresentation X.pol X.f N,
      IsClosedImmersion F'.toProj ∧ Scheme.Modules.IsSectionBasis X.f X.pol F'.σ ∧ ∀ i, F'.σ i = X.frame.σ (π i) := by
  classical

  have hmul : ∀ (α β : Fin (N + 1) ≃ Fin (N + 1)),
      ((α.toPEquiv.toMatrix : Matrix (Fin (N + 1)) (Fin (N + 1)) S) * β.toPEquiv.toMatrix) = (α.trans β).toPEquiv.toMatrix := by
    intro α β
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
  have hU : IsUnit (π.toPEquiv.toMatrix : Matrix (Fin (N + 1)) (Fin (N + 1)) S) :=
    ⟨⟨π.toPEquiv.toMatrix, π.symm.toPEquiv.toMatrix,
      by rw [hmul, Equiv.self_trans_symm, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl],
      by rw [hmul, Equiv.symm_trans_self, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]⟩, rfl⟩
  obtain ⟨X', P', h₁, h₂, -, hσ⟩ :=
    AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isReframe X (π.toPEquiv.toMatrix) hU
  refine ⟨P', h₁, h₂, fun i => ?_⟩
  rw [hσ i, Finset.sum_eq_single (π i)]
  · rw [PEquiv.toMatrix_apply, if_pos (by simp), map_one, map_one, one_smul]
  · intro j _ hj
    rw [PEquiv.toMatrix_apply, if_neg (by simpa [eq_comm] using hj), map_zero, map_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h
