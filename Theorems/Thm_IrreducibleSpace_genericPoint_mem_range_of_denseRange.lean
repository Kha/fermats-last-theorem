import Mathlib
import P2M.Util
import P2M.Sol.S_IrreducibleSpace_genericPoint_mem_range_of_denseRange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem IrreducibleSpace.genericPoint_mem_range_of_denseRange
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NoetherianSpace X] [QuasiSober X] [QuasiSober Y] [IrreducibleSpace Y] [T0Space Y]
    {f : X → Y} (hf : Continuous f) (hd : DenseRange f) :
    genericPoint Y ∈ Set.range f := by p2m_exact_reverting @_root_.P2MW.S_IrreducibleSpace_genericPoint_mem_range_of_denseRange.solution
