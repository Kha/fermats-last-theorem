import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.exists_isClosedImmersion_levelSet
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U₀ : C.Opens) (hU₀ : IsAffineOpen U₀) (f : Γ(C, U₀))
    (S : Type u) [CommRing S] [Algebra R S] (s : S)
    (hfin : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
      Module.Finite S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))})) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
    ∃ ι : Spec (CommRingCat.of (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))})) ⟶ pullback c (specMap R S),
      IsClosedImmersion ι ∧ ι ≫ baseChange R c S = specMap S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))}) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet.solution
