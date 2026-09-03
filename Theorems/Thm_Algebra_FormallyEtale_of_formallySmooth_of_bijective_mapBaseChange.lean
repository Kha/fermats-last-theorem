import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallyEtale_of_formallySmooth_of_bijective_mapBaseChange

theorem Algebra.FormallyEtale.of_formallySmooth_of_bijective_mapBaseChange
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallySmooth R T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallyEtale_of_formallySmooth_of_bijective_mapBaseChange.solution
