import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_QuasiFiniteAt_of_minimal_of_maximal

theorem Algebra.QuasiFiniteAt.of_minimal_of_maximal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (𝔮 : Ideal S) [𝔮.IsPrime]
    (hmin : Minimal
      (fun P : Ideal S => P.IsPrime ∧ P.comap (algebraMap R S) = 𝔮.comap (algebraMap R S)) 𝔮)
    (hmax : Maximal
      (fun P : Ideal S => P.IsPrime ∧ P.comap (algebraMap R S) = 𝔮.comap (algebraMap R S)) 𝔮) :
    Algebra.QuasiFiniteAt R 𝔮 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_QuasiFiniteAt_of_minimal_of_maximal.solution
