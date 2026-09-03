import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_FiniteAdeleRing_exists_monoidHom_units_classGroup_surjective_ker_eq

theorem IsDedekindDomain.FiniteAdeleRing.exists_monoidHom_units_classGroup_surjective_ker_eq
    (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ φ : (FiniteAdeleRing R K)ˣ →* ClassGroup R, Function.Surjective φ ∧
      φ.ker = IsDedekindDomain.FiniteAdeleRing.unitIdeles R K ⊔
        (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K)).range := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_monoidHom_units_classGroup_surjective_ker_eq.solution
