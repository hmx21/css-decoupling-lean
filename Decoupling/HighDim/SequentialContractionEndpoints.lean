import Decoupling.HighDim.SequentialContractionProgram

/-!
# Top, bottom, empty and native-complex endpoints

HD016, Appendix C4 “Inverting Γ up to homotopy”.  The lowest component
vanishes because the previous module is zero; its right side is proved
zero from exactness, rather than assumed zero.
-/
namespace Decoupling.HighDim.SequentialContraction
open Matrix AlgorithmTwoFiniteComplex
variable {R : Type*} [CommRing R] {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- At the top the zero initial homotopy gives precisely the degree identity. -/
theorem top_rhs (degree : Vector ℤ n) (top : ℤ) (d : Matrix (Fin n) (Fin n) R) :
    rhs degree top d 0 = fun i j =>
      if degree.get j = top then (1 : Matrix (Fin n) (Fin n) R) i j else 0 := by
  unfold SequentialContraction.rhs
  rw [Matrix.zero_mul, sub_zero]

/-- At the lowest present degree the target of h is the zero module. -/
theorem bottom_component_zero (degree : Vector ℤ n) (bottom : ℤ)
    (hb : ∀ i, bottom ≤ degree.get i) (X : Matrix (Fin n) (Fin n) R) :
    component degree bottom X = 0 := by
  funext i j
  have hi := hb i
  simp [component, show degree.get i ≠ bottom-1 by omega]

/-- The last right side vanishes as a consequence of exactness and the
previous equation. No endpoint condition is supplied to the algorithm. -/
theorem bottom_rhs_zero (degree : Vector ℤ n) (bottom : ℤ)
    (d H : Matrix (Fin n) (Fin n) R)
    (hb : ∀ i, bottom ≤ degree.get i) (hd : Homogeneous degree degree 1 d)
    (hH : Homogeneous degree degree (-1) H) (hsq : d * d = 0)
    (hex : Exact d) (hprev : Above degree bottom d H) :
    rhs degree bottom d H = 0 := by
  obtain ⟨X,hX⟩ := rhs_solvable degree bottom d H hd hsq hex hprev
  have he := component_equation degree bottom d H X hd hH hX
  rw [bottom_component_zero degree bottom hb, Matrix.mul_zero] at he
  exact he.symm

/-- Zero total rank is included without any nonempty-index assumption. -/
theorem empty_equation (d H : Matrix (Fin 0) (Fin 0) R) : d * H + H * d = 1 := by
  funext i
  exact Fin.elim0 i

end Decoupling.HighDim.SequentialContraction
