import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_ArchSemilocal
import P2M.Util
import P2M.Sol.S_AutomorphicForm_TransversalMeasure_archSemiLocalIdele_unitsAct_eq_placeEquivAlg_congr_symm

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

theorem AutomorphicForm.TransversalMeasure.archSemiLocalIdele_unitsAct_eq_placeEquivAlg_congr_symm
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (v : InfinitePlace K)
    (t : (AdeleRing (𝓞 L) L)ˣ) :
    ((AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t) :
        ((w : v.Extension L) → w.1.Completion)ˣ) : (w : v.Extension L) → w.1.Completion) =
      M4aHerbrand.ArchSemilocal.placeEquivAlg (K := K) (L := L) v
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : v.Completion ≃ₐ[v.Completion] v.Completion) σ)
          ((M4aHerbrand.ArchSemilocal.placeEquivAlg (K := K) (L := L) v).symm
            ((AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t : ((w : v.Extension L) → w.1.Completion)ˣ) :
              (w : v.Extension L) → w.1.Completion))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_TransversalMeasure_archSemiLocalIdele_unitsAct_eq_placeEquivAlg_congr_symm.solution
