import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_FiniteAdeleRing_nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range

theorem IsDedekindDomain.FiniteAdeleRing.nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range
    (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    Nonempty (ClassGroup R ≃* (FiniteAdeleRing R K)ˣ ⧸
      (IsDedekindDomain.FiniteAdeleRing.unitIdeles R K ⊔
        (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K)).range)) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range.solution
