import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_ThetaPt_one_act

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.ThetaPt.one_act
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    {𝓛 : A.Modules} {R : Type} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}
    (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)) :
    (1 : ThetaPt f L 𝓛 t).act s = s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_ThetaPt_one_act.solution
