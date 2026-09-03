import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType

open AlgebraicGeometry CategoryTheory

theorem solution
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    [AlgebraicGeometry.FormallyUnramified f] [AlgebraicGeometry.LocallyOfFiniteType f] :
    AlgebraicGeometry.LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff]
  intro U hU V hV e
  have hu : (f.appLE U V e).hom.FormallyUnramified := f.formallyUnramified_appLE hU hV e
  have hft : (f.appLE U V e).hom.FiniteType := f.finiteType_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite Γ(Y, U) Γ(X, V))
