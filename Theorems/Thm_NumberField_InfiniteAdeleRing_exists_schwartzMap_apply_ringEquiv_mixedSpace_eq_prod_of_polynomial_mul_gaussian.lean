import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian

set_option autoImplicit false

open NumberField NumberField.InfinitePlace
open scoped SchwartzMap

open scoped Classical in

theorem NumberField.InfiniteAdeleRing.exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian
    (F : Type) [Field F] [NumberField F]
    (Φ : (w : InfinitePlace F) → (Fin 2 → w.Completion) → ℂ)
    (_hΦ : ∀ w : InfinitePlace F, ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ, ∀ y : Fin 2 → w.Completion,
        Φ w y = MvPolynomial.eval
              (Sum.elim (fun i => Completion.extensionEmbedding w (y i))
                (fun i => starRingEnd ℂ (Completion.extensionEmbedding w (y i)))) P
            * Complex.exp (-(Real.pi : ℂ) * ∑ i, (((‖y i‖ ^ 2 : ℝ)) : ℂ))) :
    ∃ g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ),
      ∀ y : Fin 2 → InfiniteAdeleRing F,
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i)) = ∏ w, Φ w (fun i => y i w) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian.solution
