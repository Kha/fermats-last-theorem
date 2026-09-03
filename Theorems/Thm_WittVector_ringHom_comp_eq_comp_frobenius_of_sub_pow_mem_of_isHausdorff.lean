import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_ringHom_comp_eq_comp_frobenius_of_sub_pow_mem_of_isHausdorff

set_option autoImplicit false

theorem WittVector.ringHom_comp_eq_comp_frobenius_of_sub_pow_mem_of_isHausdorff
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (O : Type) [CommRing O] [Algebra 𝒪 O] [IsHausdorff (Ideal.span {algebraMap 𝒪 O π}) O]
    (hp : ((p : ℕ) : O) ∈ Ideal.span {algebraMap 𝒪 O π})
    (Fr : O →+* O) (hFr : ∀ x : O, Fr x - x ^ p ∈ Ideal.span {algebraMap 𝒪 O π})
    (ι : WittVector p k →+* O) :
    Fr.comp ι = ι.comp WittVector.frobenius := by p2m_exact_reverting @_root_.P2MW.S_WittVector_ringHom_comp_eq_comp_frobenius_of_sub_pow_mem_of_isHausdorff.solution
