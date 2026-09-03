import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_FormalGroup_ker_evalSeries_eq_span

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing
  HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem FormalGroup.ker_evalSeries_eq_span
    {T : Type u} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T] (a : T) (ha : a ∈ maximalIdeal T)
    (e : PowerSeries T →+* T)
    (he : ∀ f : PowerSeries T, (letI : WithIdeal T := ⟨maximalIdeal T⟩; FormalGroup.evalSeries f a) = e f) :
    RingHom.ker e = Ideal.span {PowerSeries.X - PowerSeries.C a} := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_ker_evalSeries_eq_span.solution
