import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_M4aHerbrand_IdeleGaloisDescent_exists_mulDistribMulAction_smul_eq_classAct

set_option autoImplicit false
open NumberField M4aHerbrand

theorem M4aHerbrand.IdeleGaloisDescent.exists_mulDistribMulAction_smul_eq_classAct
    (E F : Type*) [Field E] [Field F] [NumberField F] [Algebra E F]
    (D : IdeleGaloisDescent (𝓞 F) E F) :
    ∃ (_ : MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)),
      ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_mulDistribMulAction_smul_eq_classAct.solution
