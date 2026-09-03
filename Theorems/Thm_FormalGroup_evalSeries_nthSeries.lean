import Mathlib
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_FormalGroup_evalSeries_nthSeries

theorem FormalGroup.evalSeries_nthSeries {R : Type*} [CommRing R] {A : Type*} [CommRing A] [UniformSpace A] [Algebra R A]
    [IsUniformAddGroup A] [CompleteSpace A] [T2Space A] [IsTopologicalRing A] [IsLinearTopology A A]
    (F : FormalGroup R) {x : A} (hx : IsTopologicallyNilpotent x) (n : ℕ) :
    FormalGroup.evalSeries (F.nthSeries n) x = F.evalNSMul n x := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_evalSeries_nthSeries.solution
