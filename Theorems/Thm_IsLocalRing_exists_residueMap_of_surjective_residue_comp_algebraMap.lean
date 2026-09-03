import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_residueMap_of_surjective_residue_comp_algebraMap

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_residueMap_of_surjective_residue_comp_algebraMap
    (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (k : Type) [Field k]
    (res₀ : Λ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal Λ)
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra Λ T]
    (hT : Function.Surjective (⇑(residue T) ∘ ⇑(algebraMap Λ T))) :
    ∃ resT : T →+* k, Function.Surjective resT ∧ RingHom.ker resT = maximalIdeal T ∧
      ∀ w : Λ, resT (algebraMap Λ T w) = res₀ w := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_residueMap_of_surjective_residue_comp_algebraMap.solution
