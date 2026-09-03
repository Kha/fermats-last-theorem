import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_irreducibleSpace_and_topologicalKrullDim_pullback_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.irreducibleSpace_and_topologicalKrullDim_pullback_eq_one
    {K₁ : Type} [Field K₁] [IsAlgClosed K₁] {F : Type} [Field F] [Algebra K₁ F]
    (𝔐 : AlgebraicCurve.CurveModel K₁ F)
    {B : Type} [CommRing B] (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B))
    (sbar : Spec (CommRingCat.of K₁) ⟶ Spec (CommRingCat.of B))
    (e𝔐 : 𝔐.C ⟶ Limits.pullback πX sbar) [IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ Limits.pullback.snd πX sbar = 𝔐.toBase)
    (k : Type) [Field k] (j : K₁ →+* k) :
    IrreducibleSpace ↑(Limits.pullback πX (Spec.map (CommRingCat.ofHom j) ≫ sbar)) ∧
    topologicalKrullDim ↑(Limits.pullback πX (Spec.map (CommRingCat.ofHom j) ≫ sbar)) = 1 ∧
    LocallyOfFiniteType (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom j) ≫ sbar)) ∧
    QuasiCompact (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom j) ≫ sbar)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_irreducibleSpace_and_topologicalKrullDim_pullback_eq_one.solution
