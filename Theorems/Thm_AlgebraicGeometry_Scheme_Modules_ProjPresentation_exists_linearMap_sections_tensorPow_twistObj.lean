import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj

universe u

open CategoryTheory Opposite AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A)} {L : X.Modules}
    (𝔓 : L.ProjPresentation f N) (m : ℕ) :
    ∃ e : ∀ U : X.Opens, Γ(L.tensorPow m, U) →ₗ[Γ(X, U)] ProjSpace.twistObj f 𝔓.toProj m U,
      (∀ (U : X.Opens) (x : Γ(L.tensorPow m, U)) (i : Fin (N + 1)),
          ((e U x).val i) •
              (L.tensorPow m).presheaf.map (homOfLE (le_top : U ⊓ ProjSpace.pullbackChart 𝔓.toProj i ≤ ⊤)).op
                (Scheme.Modules.tensorPowSection (𝔓.σ i) m) =
            (L.tensorPow m).presheaf.map (homOfLE (inf_le_left : U ⊓ ProjSpace.pullbackChart 𝔓.toProj i ≤ U)).op x) ∧
      (∀ (U U' : X.Opens) (h : U ≤ U') (x : Γ(L.tensorPow m, U')),
          e U ((L.tensorPow m).presheaf.map (homOfLE h).op x) = ProjSpace.twistRes f 𝔓.toProj m h (e U' x)) ∧
      (∀ (U : X.Opens) (i : Fin (N + 1)), U ≤ ProjSpace.pullbackChart 𝔓.toProj i → Function.Bijective (e U)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj.solution
