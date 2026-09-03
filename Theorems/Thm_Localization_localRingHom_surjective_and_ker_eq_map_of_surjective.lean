import Mathlib
import P2M.Util
import P2M.Sol.S_Localization_localRingHom_surjective_and_ker_eq_map_of_surjective

set_option autoImplicit false

theorem Localization.localRingHom_surjective_and_ker_eq_map_of_surjective
    {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Surjective f)
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] (hpq : p = Ideal.comap f q) :
    Function.Surjective (Localization.localRingHom p q f hpq) ∧
      RingHom.ker (Localization.localRingHom p q f hpq) =
        Ideal.map (algebraMap A (Localization.AtPrime p)) (RingHom.ker f) := by p2m_exact_reverting @_root_.P2MW.S_Localization_localRingHom_surjective_and_ker_eq_map_of_surjective.solution
