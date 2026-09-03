import Mathlib
import Definitions.Def_RingTheory_AffineDilatation
import P2M.Util
import P2M.Sol.S_AffineDilatation_nonempty_algEquiv_tensorProduct_of_flat_of_map_eq

set_option autoImplicit false

open TensorProduct

universe u

theorem AffineDilatation.nonempty_algEquiv_tensorProduct_of_flat_of_map_eq
    {P : Type u} [CommRing P] (I : Ideal P) (a : P) (ha : a ∈ I)
    {C : Type u} [CommRing C] [Algebra P C] [Module.Flat P C]
    (J : Ideal C) (b : C) (hJ : I.map (algebraMap P C) = J) (hb : algebraMap P C a = b) :
    ∃ e : C ⊗[P] AffineDilatation.Ring I a ≃ₐ[C] AffineDilatation.Ring J b,
      ∀ (g : P) (hg : g ∈ I),
        e (1 ⊗ₜ AffineDilatation.divElem I a g hg) =
          AffineDilatation.divElem J b (algebraMap P C g) (hJ ▸ Ideal.mem_map_of_mem (algebraMap P C) hg) := by p2m_exact_reverting @_root_.P2MW.S_AffineDilatation_nonempty_algEquiv_tensorProduct_of_flat_of_map_eq.solution
