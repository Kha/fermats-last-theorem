import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_FiniteAdeleRing_unitIdelesOutside_sup_range_eq_top

set_option autoImplicit false
open scoped nonZeroDivisors
theorem IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside_sup_range_eq_top
    (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum R))
    (hS : ∀ c : ClassGroup R, ∃ I : (Ideal R)⁰, ClassGroup.mk0 I = c ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum R, v.asIdeal ∣ (I : Ideal R) → v ∈ S) :
    IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S ⊔
      (Units.map (algebraMap K (IsDedekindDomain.FiniteAdeleRing R K) :
        K →* IsDedekindDomain.FiniteAdeleRing R K)).range = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_unitIdelesOutside_sup_range_eq_top.solution
