import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure
import P2M.Util
import P2M.Sol.S_TwistedUnipotentTerm_isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem TwistedUnipotentTerm.isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) ∧
      IsOpen (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) ∧
      ∀ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
        ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v ↔
          ∀ w : v.Extension (𝓞 L),
            Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ : (w.1.adicCompletion L)ˣ) :
              w.1.adicCompletion L) = 1 := by p2m_exact_reverting @_root_.P2MW.S_TwistedUnipotentTerm_isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one.solution
