import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_one_le_ramificationIndexAlong
set_option autoImplicit false

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "algebraAlong isIntegral_along Place.ramificationIndexAlong Place" namespace Place p2m_export "AlgebraicCurve.Place" "ramificationIndexAlong ramificationIndex_pos" end AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in
private theorem AlgebraicCurve.Place.solution_impl
    {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : AlgebraicCurve.Place K F') :
    1 ≤ AlgebraicCurve.Place.ramificationIndexAlong φ w := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : AlgebraicCurve.Place K F') :
    1 ≤ AlgebraicCurve.Place.ramificationIndexAlong φ w :=
  AlgebraicCurve.Place.solution_impl φ hφ w
