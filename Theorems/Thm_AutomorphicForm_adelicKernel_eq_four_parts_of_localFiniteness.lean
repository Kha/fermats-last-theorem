import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicKernel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_adelicKernel_eq_four_parts_of_localFiniteness

set_option autoImplicit false

open Matrix

open scoped NumberField
theorem AutomorphicForm.adelicKernel_eq_four_parts_of_localFiniteness
    (F : Type) [Field F] [NumberField F] {M : Type*} [AddCommMonoid M]
    (h : AutomorphicForm.AdelicKernelLocalFiniteness F)
    {f : AutomorphicForm.AdelicGL2 (𝓞 F) F → M}
    {C : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)}
    (hC : IsCompact C) (hsupp : Function.support f ⊆ C)
    (x y : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    AutomorphicForm.adelicKernel F f x y
      = AutomorphicForm.adelicKernelCentralPart F f x y
        + AutomorphicForm.adelicKernelEllipticPart F f x y
        + AutomorphicForm.adelicKernelHyperbolicPart F f x y
        + AutomorphicForm.adelicKernelUnipotentPart F f x y := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_adelicKernel_eq_four_parts_of_localFiniteness.solution
