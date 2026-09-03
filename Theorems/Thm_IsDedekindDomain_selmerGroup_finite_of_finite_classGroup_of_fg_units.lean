import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.ClassGroup
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_selmerGroup_finite_of_finite_classGroup_of_fg_units

open IsDedekindDomain

universe u v
theorem IsDedekindDomain.selmerGroup.finite_of_finite_classGroup_of_fg_units
    {R : Type u} [CommRing R] [IsDedekindDomain R] {K : Type v} [Field K] [Algebra R K]
    [IsFractionRing R K] {S : Set (HeightOneSpectrum R)} {n : ℕ} [hn : Fact (0 < n)]
    [Finite (ClassGroup R)] [Monoid.FG Rˣ] [Finite S] :
    Finite (selmerGroup (R := R) (K := K) (S := S) (n := n)) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_selmerGroup_finite_of_finite_classGroup_of_fg_units.solution
