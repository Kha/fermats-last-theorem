import Mathlib
import P2M.Util
import P2M.Sol.S_DeligneSerre_OperatorAlgebra_exists_eigenvector_baseChange_of_algHom

set_option autoImplicit false

open scoped TensorProduct

theorem DeligneSerre.OperatorAlgebra.exists_eigenvector_baseChange_of_algHom
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {M : Type*} [AddCommGroup M] [Module 𝒪 M] [Module.Finite 𝒪 M] [Module.IsTorsionFree 𝒪 M]
    {T : Type*} [CommRing T] [Algebra 𝒪 T]
    (act : T →ₐ[𝒪] Module.End 𝒪 M) (hact : Function.Injective act)
    {G : Type*} [CommGroup G] (d : G →* Module.End 𝒪 M)
    (hd : ∀ (g : G) (t : T), d g * act t = act t * d g)
    {F : Type*} [Field F] [IsAlgClosed F] [Algebra 𝒪 F]
    (hF : Function.Injective (algebraMap 𝒪 F)) (lam : T →ₐ[𝒪] F) :
    ∃ (e : G →* Fˣ) (w : F ⊗[𝒪] M), w ≠ 0 ∧
      (∀ t : T, (act t).baseChange F w = lam t • w) ∧
      (∀ g : G, (d g).baseChange F w = ((e g : Fˣ) : F) • w) := by p2m_exact_reverting @_root_.P2MW.S_DeligneSerre_OperatorAlgebra_exists_eigenvector_baseChange_of_algHom.solution
