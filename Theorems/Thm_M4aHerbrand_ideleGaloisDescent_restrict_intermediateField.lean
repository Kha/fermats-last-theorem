import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_M4aHerbrand_ideleGaloisDescent_restrict_intermediateField

set_option autoImplicit false

theorem M4aHerbrand.ideleGaloisDescent_restrict_intermediateField
    (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
    [Algebra R F] [IsFractionRing R F] [Algebra E F]
    (D : M4aHerbrand.IdeleGaloisDescent R E F) (E' : IntermediateField E F) :
    (∀ (D' : M4aHerbrand.IdeleGaloisDescent R E' F) (g : F ≃ₐ[E'] F),
        D'.act g = D.act (g.restrictScalars E)) ∧
    (∀ (D' : M4aHerbrand.IdeleGaloisDescent R E' F) (g : F ≃ₐ[E'] F)
        (c : M4aHerbrand.IdeleClassGroup R F),
        D'.classAct g c = D.classAct (g.restrictScalars E) c) ∧
    Nonempty (M4aHerbrand.IdeleGaloisDescent R E' F) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_ideleGaloisDescent_restrict_intermediateField.solution
