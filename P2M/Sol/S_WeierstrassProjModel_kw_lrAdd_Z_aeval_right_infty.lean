import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import P2M.Util
namespace P2MW.S_WeierstrassProjModel_kw_lrAdd_Z_aeval_right_infty

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option linter.unusedSimpArgs false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem solution {A : Type u} [CommRing A] [Algebra R A] (P : Fin 3 → A) :
    MvPolynomial.aeval (R := R) (Sum.elim P ![(0:A), 1, 0]) (kw_lrAdd_Z W)
      = P 2 ^ 2 := by
  simp only [kw_lrAdd_Z, kw_lrAdd_starZ, kw_lrAdd_c₁₂, kw_lrAdd_c₂₁,
    map_sub, map_add, map_mul, map_neg, map_pow, aeval_X, aeval_C,
    Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

end
