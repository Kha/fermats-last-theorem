import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_surjective_and_finrank_and_ker_tensorProduct_map_transition

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.surjective_and_finrank_and_ker_tensorProduct_map_transition
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] {h : ℕ} (H : PDivisibleGroup O p h)
    (k : Type) [CommRing k] [Nontrivial k] [Algebra O k] :
    (∀ v : ℕ, Function.Surjective
      (Bialgebra.TensorProduct.map (BialgHom.id k k) (H.transition v))) ∧
    (∀ v : ℕ, Module.finrank k (k ⊗[O] H.level v) = p ^ (v * h)) ∧
    (∀ v : ℕ, RingHom.ker (Bialgebra.TensorProduct.map (BialgHom.id k k) (H.transition v)) =
      PDivisibleGroup.Hopf.torsionIdeal k (k ⊗[O] H.level (v + 1)) (p ^ v)) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_surjective_and_finrank_and_ker_tensorProduct_map_transition.solution
