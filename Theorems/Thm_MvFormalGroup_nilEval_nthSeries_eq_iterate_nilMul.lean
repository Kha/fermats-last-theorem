import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
import P2M.Sol.S_MvFormalGroup_nilEval_nthSeries_eq_iterate_nilMul
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast

set_option autoImplicit false

open MvPowerSeries

theorem MvFormalGroup.nilEval_nthSeries_eq_iterate_nilMul
    {B : Type} [CommRing B] {g : ℕ} (F : MvFormalGroup g B)
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (ν : ℕ) (hJ : J ^ (ν + 1) = ⊥)
    (s : Fin g → B') (hs : ∀ i, s i ∈ J) (m : ℕ) (i : Fin g) :
    MvFormalGroup.nilEval ν (F.nthSeries m i) s = ((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) i := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_nilEval_nthSeries_eq_iterate_nilMul.solution
