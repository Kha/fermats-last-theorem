import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_smoothOfRelativeDimension_one
attribute [-instance] AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp] AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.isInvertible_I_of_smoothOfRelativeDimension_one
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {K : Type u} [Field K] {gK : Spec (CommRingCat.of K) ⟶ S}
    [IsSeparated (pullback.snd f gK)] [SmoothOfRelativeDimension 1 (pullback.snd f gK)]
    {r : ℕ} (E : RelEffCartierDiv f r gK) :
    E.I.IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_smoothOfRelativeDimension_one.solution
