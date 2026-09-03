import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_eq_of_forall_toAlgHom_comp_eq_of_ringOfIntegers

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.eq_of_forall_toAlgHom_comp_eq_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h h' : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (H : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h')
    (φ φ' : ∀ v : ℕ, H.level v →ₐc[PadicAlgCl.ringOfIntegers p K] G.level v)
    (hφ : ∀ (v : ℕ) (x : G.Point (PadicAlgCl p) v),
      (PDivisibleGroup.Point.toAlgHom x).comp (φ v : H.level v →ₐ[PadicAlgCl.ringOfIntegers p K] G.level v) =
        (PDivisibleGroup.Point.toAlgHom x).comp (φ' v : H.level v →ₐ[PadicAlgCl.ringOfIntegers p K] G.level v)) :
    φ = φ' := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_eq_of_forall_toAlgHom_comp_eq_of_ringOfIntegers.solution
