import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq

set_option autoImplicit false
theorem AutomorphicForm.exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq
    (F : Type) [Field F] [NumberField F] :
    ∃ R : Finset ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ),
      ∀ g : Matrix.GeneralLinearGroup (Fin 2)
        (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F),
        ∃ a ∈ R, ∃ d : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ,
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
            Valued.v ((d : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v) =
              max
                (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 0 *
                    ((a⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ) :
                      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v))
                (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 1) v))) ∧
          AutomorphicForm.contentHomFin F a * AutomorphicForm.contentHomFin F d ^ 2 =
            AutomorphicForm.contentHomFin F (Matrix.GeneralLinearGroup.det g) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq.solution
