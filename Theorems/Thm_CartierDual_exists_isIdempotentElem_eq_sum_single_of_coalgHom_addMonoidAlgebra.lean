import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_CartierDual_exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra

set_option autoImplicit false

universe u v w

open IsLocalRing
open scoped TensorProduct

theorem CartierDual.exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra
    {S : Type u} [CommRing S] {B : Type v} [CommRing B] [Bialgebra S B] [Module.Finite S B] [Module.Free S B]
    (M : Type w) [Fintype M] [DecidableEq M]
    (f : B →ₗc[S] AddMonoidAlgebra S M) :
    ∃ e : M → CartierDual S B,
      (∀ m, IsIdempotentElem (e m)) ∧ (∀ a b, a ≠ b → e a * e b = 0) ∧ ∑ m, e m = 1 ∧
      ∀ b : B, f b = ∑ m, AddMonoidAlgebra.single m (e m b) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra.solution
