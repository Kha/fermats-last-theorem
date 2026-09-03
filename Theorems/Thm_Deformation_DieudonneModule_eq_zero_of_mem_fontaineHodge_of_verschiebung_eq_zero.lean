import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_eq_zero_of_mem_fontaineHodge_of_verschiebung_eq_zero

universe u v w

theorem Deformation.DieudonneModule.eq_zero_of_mem_fontaineHodge_of_verschiebung_eq_zero
    {ℛ : Type u} [CommRing ℛ] (p : ℕ) [Fact p.Prime] (hp : (p : ℛ) ∈ nonZeroDivisors ℛ)
    {R : Type v} [CommRing R] {A : Type w} [CommRing A] [Bialgebra R A]
    (π : ℛ →+* A) (hker : RingHom.ker π = Ideal.span {(p : ℛ)})
    {z : Deformation.DieudonneModule R p A} (hz : z ∈ Deformation.fontaineHodge R p π)
    (hV : Deformation.DieudonneModule.verschiebung R p A z = 0) : z = 0 := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_eq_zero_of_mem_fontaineHodge_of_verschiebung_eq_zero.solution
