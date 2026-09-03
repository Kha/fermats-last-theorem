import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
namespace P2MW.S_AutomorphicForm_archIdent_tmul_apply

set_option autoImplicit false

open NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NumberField.LiesOver

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (x : L) (a : InfiniteAdeleRing K) (w : InfinitePlace L) :
    letI : w.1.LiesOver (w.comap (algebraMap K L)).1 := ⟨rfl⟩
    archIdent K L (x ⊗ₜ a) w =
      algebraMap (w.comap (algebraMap K L)).Completion w.Completion (a (w.comap (algebraMap K L))) *
        algebraMap L w.Completion x := by
  letI : w.1.LiesOver (w.comap (algebraMap K L)).1 := ⟨rfl⟩
  show (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv
      ((Algebra.TensorProduct.comm K L (InfiniteAdeleRing K)) (x ⊗ₜ a)) w = _
  rw [Algebra.TensorProduct.comm_tmul, FLT.InfiniteAdeleBaseChange.InfinitePlaceData.baseChangeRingEquiv_apply]
  show M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K L)) w
      (FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv K L (a ⊗ₜ[K] x) (w.comap (algebraMap K L))) = _
  have h : FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv K L (a ⊗ₜ[K] x) (w.comap (algebraMap K L)) =
      a (w.comap (algebraMap K L)) ⊗ₜ[K] x := rfl
  rw [h, M4aHerbrand.ArchSemilocal.psiFactor_tmul]
