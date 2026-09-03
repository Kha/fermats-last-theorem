import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal

universe u v

theorem PDivisibleGroup.Hopf.exists_forall_comp_transition_surjective_ker_eq_torsionIdeal
    {𝓞 : Type u} [CommRing 𝓞] (p h : ℕ)
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v)) :
    ∃ T : ∀ v w : ℕ, L (v + w) →ₐc[𝓞] L v,
      (∀ v, T v 0 = BialgHom.id 𝓞 (L v)) ∧
      (∀ v w, T v (w + 1) = (T v w).comp (t (v + w))) ∧
      (∀ v w, Function.Surjective (T v w)) ∧
      (∀ v w, RingHom.ker (T v w) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + w)) (p ^ v)) ∧
      (∀ v, PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (L v) (p ^ v) =
        (Algebra.ofId 𝓞 (L v)).comp (Bialgebra.counitAlgHom 𝓞 (L v))) ∧
      (∀ v w, Module.Free 𝓞 (L (v + w) ⧸ PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + w)) (p ^ w)) ∧
        Module.finrank 𝓞 (L (v + w) ⧸ PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + w)) (p ^ w)) =
          p ^ (w * h)) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal.solution
