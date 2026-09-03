import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ringHom_comp_eq_of_moduleFinite_of_flat

theorem ValuationSubring.exists_ringHom_comp_eq_of_moduleFinite_of_flat
    {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Flat R B]
    {K : Type*} [Field K] [IsAlgClosed K] (O : ValuationSubring K) [Algebra R ↥O]
    {k : Type*} [Field k] (π : ↥O →+* k) (hπ : Function.Surjective π)
    (φ₀ : B →+* k) (hcomp : φ₀.comp (algebraMap R B) = π.comp (algebraMap R ↥O)) :
    ∃ φ : B →+* ↥O, φ.comp (algebraMap R B) = algebraMap R ↥O ∧ π.comp φ = φ₀ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ringHom_comp_eq_of_moduleFinite_of_flat.solution
