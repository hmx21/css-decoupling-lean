import Decoupling.PeriodicLaurent
import Decoupling.PauliUnitary

/-!
# Finite-periodic physical CNOT layers and full circuit unitaries

For every positive period, the literal integer displacements of the Laurent
circuit are reduced modulo the period. Each listed family remains a disjoint
parallel CNOT layer. The full circuit has a genuine complex Hilbert unitary,
with exactly the specialized X and Z support actions and the original word order.
-/

namespace Decoupling.PeriodicCircuit

open Matrix PeriodicLaurent PauliUnitary

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (L : ℕ) [NeZero L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Site (ι : Type*) := ι × Cell L

/-- A periodic layer's literal control and target sites. -/
def source (g : Circuit.CNOT ι) (p : Cell L) : Site L ι := (g.control, p)
def destination (g : Circuit.CNOT ι) (p : Cell L) : Site L ι :=
  (g.target, p + periodMap L g.displacement)

omit [Fintype ι] [DecidableEq ι] in
/-- Distinct species prevent gate collisions even if a displacement wraps to zero. -/
theorem layer_disjoint (g : Circuit.CNOT ι) {p q : Cell L} (h : p ≠ q) :
    source L g p ≠ source L g q ∧ source L g p ≠ destination L g q ∧
    destination L g p ≠ source L g q ∧ destination L g p ≠ destination L g q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun e => h (congrArg Prod.snd e)
  · exact fun e => g.distinct (congrArg Prod.fst e)
  · exact fun e => g.distinct (congrArg Prod.fst e).symm
  · exact fun e => h (add_right_cancel (congrArg Prod.snd e))

omit [Fintype ι] in
private theorem matrix_single_apply (i j a b : ι) (r : R) (p q : Cell L) :
    matrix L (Matrix.single i j r) (a, p) (b, q) =
      if a = i ∧ b = j then scalar L r p q else 0 := by
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp_all [Matrix.single, eq_comm]

/-- The specialized matrix is exactly the simultaneous classical CNOT update. -/
theorem layer_apply (g : Circuit.CNOT ι) (s : Bits (Site L ι)) (i : ι) (p : Cell L) :
    (matrix L g.xMatrix *ᵥ s) (i, p) =
      s (i, p) + if i = g.target then s (g.control, p - periodMap L g.displacement) else 0 := by
  rw [Circuit.CNOT.xMatrix, matrix_add, matrix_one, Matrix.add_mulVec, Matrix.one_mulVec]
  change s (i, p) + _ = _
  congr 1
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, matrix_single_apply]
  by_cases h : i = g.target
  · subst i
    simp [scalar_monomial, ite_mul, ← sub_eq_iff_eq_add]
  · simp [h]

/-- The actual finite binary automorphism implemented by the full Laurent word. -/
def binary (c : List (Circuit.CNOT ι)) : Bits (Site L ι) ≃ₗ[ZMod 2] Bits (Site L ι) where
  toLinearMap := (matrix L (Circuit.xAction c)).mulVecLin
  invFun := (matrix L (Circuit.xAction c.reverse)).mulVec
  left_inv s := by
    change matrix L (Circuit.xAction c.reverse) *ᵥ (matrix L (Circuit.xAction c) *ᵥ s) = s
    rw [Matrix.mulVec_mulVec, ← matrix_mul]
    have h := Circuit.xAction_reverse c.reverse
    rw [List.reverse_reverse] at h
    rw [h, matrix_one, Matrix.one_mulVec]
  right_inv s := by
    change matrix L (Circuit.xAction c) *ᵥ (matrix L (Circuit.xAction c.reverse) *ᵥ s) = s
    rw [Matrix.mulVec_mulVec, ← matrix_mul, Circuit.xAction_reverse, matrix_one, Matrix.one_mulVec]

@[simp] theorem binary_apply (c : List (Circuit.CNOT ι)) (s : Bits (Site L ι)) :
    binary L c s = matrix L (Circuit.xAction c) *ᵥ s := rfl

/-- The Z action is the literal inverse transpose of the finite X action. -/
theorem binary_inverseTranspose (c : List (Circuit.CNOT ι)) (b : Bits (Site L ι)) :
    inverseTranspose (binary L c) b = matrix L (Circuit.zAction c) *ᵥ b := by
  rw [Circuit.zAction_eq_inverse_dagger, matrix_dagger]
  unfold inverseTranspose
  have h : LinearMap.toMatrix' (binary L c).symm.toLinearMap =
      matrix L (Circuit.xAction c.reverse) := LinearMap.toMatrix'_toLin' _
  rw [h]

/-- Genuine complex matrix of the whole word. -/
def unitary (c : List (Circuit.CNOT ι)) : Matrix.unitaryGroup (Bits (Site L ι)) ℂ :=
  permutationUnitary (binary L c).toEquiv

/-- The same operation on the actual finite complex Hilbert space. -/
def hilbertUnitary (c : List (Circuit.CNOT ι)) : Hilbert (Site L ι) ≃ₗᵢ[ℂ] Hilbert (Site L ι) :=
  hilbertPermutation (binary L c).toEquiv

theorem conjugate_X_word (c : List (Circuit.CNOT ι)) (a : Bits (Site L ι)) :
    (unitary L c : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ) * X a * (unitary L c : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ)ᴴ =
      X (matrix L (Circuit.xAction c) *ᵥ a) := conjugate_X (binary L c) a

theorem conjugate_Z_word (c : List (Circuit.CNOT ι)) (b : Bits (Site L ι)) :
    (unitary L c : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ) * Z b * (unitary L c : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ)ᴴ =
      Z (matrix L (Circuit.zAction c) *ᵥ b) := by
  change permutation (binary L c).toEquiv * Z b * (permutation (binary L c).toEquiv)ᴴ = _
  rw [conjugate_Z, binary_inverseTranspose]

/-- A layer acts on each computational ket by its simultaneous periodic CNOT update. -/
theorem layer_ket (g : Circuit.CNOT ι) (s : Bits (Site L ι)) :
    (unitary L [g] : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ) *ᵥ ket s =
      ket (fun t => s t + if t.1 = g.target then
        s (g.control, t.2 - periodMap L g.displacement) else 0) := by
  rw [show (unitary L [g] : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ) = permutation (binary L [g]).toEquiv from rfl,
    permutation_ket]
  congr 1
  funext t
  change (binary L [g] s) t = _
  rw [binary_apply, Circuit.xAction_cons, Circuit.xAction_nil, Matrix.mul_one]
  exact layer_apply L g s t.1 t.2


/-- Exact ordering of binary operations: the rightmost listed layer acts first. -/
theorem binary_cons (g : Circuit.CNOT ι) (c : List (Circuit.CNOT ι)) :
    binary L (g :: c) = (binary L c).trans (binary L [g]) := by
  apply LinearEquiv.ext
  intro s
  change matrix L (Circuit.xAction (g :: c)) *ᵥ s =
    matrix L (Circuit.xAction [g]) *ᵥ (matrix L (Circuit.xAction c) *ᵥ s)
  rw [Circuit.xAction_cons, Circuit.xAction_cons, Circuit.xAction_nil,
    Matrix.mul_one, matrix_mul, Matrix.mulVec_mulVec]

/-- The actual complex unitary is the ordered product of its parallel layers. -/
theorem unitary_cons (g : Circuit.CNOT ι) (c : List (Circuit.CNOT ι)) :
    (unitary L (g :: c) : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ) =
      (unitary L [g] : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ) * (unitary L c : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ) := by
  change permutation (binary L (g :: c)).toEquiv =
    permutation (binary L [g]).toEquiv * permutation (binary L c).toEquiv
  rw [binary_cons]
  apply Matrix.mulVec_injective
  funext ψ s
  simp only [← Matrix.mulVec_mulVec, permutation_apply]
  rfl

@[simp]
theorem unitary_nil : (unitary L ([] : List (Circuit.CNOT ι)) :
    Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ) = 1 := by
  have hb : binary L ([] : List (Circuit.CNOT ι)) = LinearEquiv.refl (ZMod 2) (Bits (Site L ι)) := by
    apply LinearEquiv.ext
    intro s
    simp only [binary_apply, Circuit.xAction_nil, matrix_one, Matrix.one_mulVec,
      LinearEquiv.refl_apply]
  change permutation (binary L []).toEquiv = 1
  rw [hb]
  exact Matrix.permMatrix_refl

/-- The entire unitary is the literal matrix product of the given parallel layers. -/
theorem unitary_prod (c : List (Circuit.CNOT ι)) :
    (unitary L c : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ) =
      (c.map (fun g => (unitary L [g] : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ))).prod := by
  induction c with
  | nil => simp
  | cons g c ih => rw [unitary_cons, List.map_cons, List.prod_cons, ih]

/-- Locality on the torus is witnessed by an integer lift of bounded displacement. -/
def WithinRange (r : ℕ) (p q : Cell L) : Prop :=
  ∃ a : Translation, q = p + periodMap L a ∧ ∀ i : Fin 3, (a i).natAbs ≤ r

omit [Fintype ι] [DecidableEq ι] in
/-- Wrapping never invalidates the original geometric range bound. -/
theorem layer_within_range (c : List (Circuit.CNOT ι)) (g : Circuit.CNOT ι)
    (hg : g ∈ c) (p : Cell L) :
    WithinRange L (Circuit.rangeBound c) (source L g p).2 (destination L g p).2 :=
  ⟨g.displacement, rfl, fun i => Circuit.displacement_le_rangeBound c g hg i⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The exact same layer count and integer displacement bounds work for every period. -/
theorem depth_range (c : List (Circuit.CNOT ι)) :
    ∃ depth range : ℕ, depth = c.length ∧
      ∀ g ∈ c, ∀ i : Fin 3, (g.displacement i).natAbs ≤ range :=
  Circuit.finite_depth_range c

end
end Decoupling.PeriodicCircuit
