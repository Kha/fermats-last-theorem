import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import P2M.Util
import P2M.Sol.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_archWord_eq_zero_of_not_mem

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.TwistedBruhat.exists_isCompact_forall_archWord_eq_zero_of_not_mem
    (L : Type) [Field L] [NumberField L]
    (A : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L) (hA : Continuous A) (hAs : Continuous A.symm)
    (φ : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφ : HasCompactSupport φ)
    (Ct : Set (InfiniteAdeleRing L)ˣ) (hCt : IsCompact Ct)
    (Kk : Set (GL (Fin 2) (InfiniteAdeleRing L))) (hKk : IsCompact Kk) :
    ∃ Cζ : Set (InfiniteAdeleRing L)ˣ, IsCompact Cζ ∧
      ∀ (y : InfiniteAdeleRing L) (t : (InfiniteAdeleRing L)ˣ) (k : GL (Fin 2) (InfiniteAdeleRing L))
        (ζ : (InfiniteAdeleRing L)ˣ), t ∈ Ct → k ∈ Kk → ζ ∉ Cζ →
        φ (k⁻¹ * unipotentGL2 (y * ((t⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
            diagOne (Units.map A.toRingHom.toMonoidHom t * t⁻¹) *
            Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom ζ) *
            Matrix.GeneralLinearGroup.map A.toRingHom k) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_archWord_eq_zero_of_not_mem.solution
