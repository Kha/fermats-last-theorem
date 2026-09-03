import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal

set_option autoImplicit false

open NumberField NumberField.InfinitePlace

open scoped Classical in

theorem NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal
    (K : Type) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    SignType.sign (Algebra.norm ℚ x) =
      ∏ w : {w : InfinitePlace K // w.IsReal}, SignType.sign (embedding_of_isReal w.2 x) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.solution
