import Decoupling.HighDim.StableCSS
import Decoupling.HighDim.BlockCircuit
import Decoupling.HighDim.Fourier
import Decoupling.HighDim.CSS

/-!
# Stabilizer-image certificates

Source: `drafts/main.tex`, Sections IV.A--C. The helper image-transport
arguments retain exactness explicitly. The main existence theorem below
constructs comparison data and an actual finite SUM/SWAP circuit from an
isomorphism of the actual (possibly freely stabilized) check cokernels.
`inImage B v` means membership in the column-generated submodule im B.
-/

namespace Decoupling.HighDim.PhysicalIsomorphism

open Matrix
noncomputable section

variable {K : Type*} [CommRing K] {D : ℕ}
local notation "R" => Laurent K D

def inImage {m n : Type*} [Fintype n] (B : Matrix m n R) (v : m → R) : Prop :=
  ∃ z, B *ᵥ z = v

variable {Q Q' C C' Z Z' : Type*}
  [Fintype Q] [Fintype Q'] [Fintype C] [Fintype C'] [Fintype Z] [Fintype Z']
  [DecidableEq Q] [DecidableEq Q'] [DecidableEq C] [DecidableEq C']

omit [DecidableEq Q] [DecidableEq Q'] [DecidableEq C'] in
/-- An invertible commuting square transports the physical kernel. -/
theorem kernel_transport
    (H : Matrix C Q R) (H' : Matrix C' Q' R)
    (U : Matrix Q' Q R) (P : Matrix C' C R) (Pinv : Matrix C C' R)
    (hP : Pinv * P = 1) (square : H' * U = P * H) (v : Q → R) :
    H' *ᵥ (U *ᵥ v) = 0 ↔ H *ᵥ v = 0 := by
  rw [mulVec_mulVec, square, ← mulVec_mulVec]
  constructor
  · intro h
    have hh := congrArg (fun w => Pinv *ᵥ w) h
    simpa [mulVec_mulVec, ← Matrix.mul_assoc, hP] using hh
  · intro h
    simp [h]

omit [DecidableEq Q] [DecidableEq C'] in
/-- First identity in the stabilized check square, given the two physical exactness equalities. -/
theorem z_image_certificate
    (H : Matrix C Q R) (H' : Matrix C' Q' R)
    (B : Matrix Q Z R) (B' : Matrix Q' Z' R)
    (U : Matrix Q' Q R) (Uinv : Matrix Q Q' R)
    (P : Matrix C' C R) (Pinv : Matrix C C' R)
    (hU : U * Uinv = 1) (hP : Pinv * P = 1)
    (square : H' * U = P * H)
    (exactF : ∀ v, H *ᵥ v = 0 ↔ inImage B v)
    (exactG : ∀ v, H' *ᵥ v = 0 ↔ inImage B' v) (v : Q' → R) :
    (∃ z, U *ᵥ (B *ᵥ z) = v) ↔ inImage B' v := by
  constructor
  · rintro ⟨z, rfl⟩
    apply (exactG _).mp
    apply (kernel_transport H H' U P Pinv hP square _).mpr
    exact (exactF _).mpr ⟨z, rfl⟩
  · intro h
    have hUv : U *ᵥ (Uinv *ᵥ v) = v := by simp [mulVec_mulVec, hU]
    have hz : H *ᵥ (Uinv *ᵥ v) = 0 :=
      (kernel_transport H H' U P Pinv hP square _).mp
        (by rw [hUv]; exact (exactG _).mpr h)
    obtain ⟨z, hz⟩ := (exactF _).mp hz
    exact ⟨z, by rw [hz, hUv]⟩

omit [Fintype C'] [DecidableEq Q] [DecidableEq C] [DecidableEq C'] in
/-- The dagger identity used in the second half of the paper’s stabilization construction. -/
theorem dagger_check_identity
    (H : Matrix C Q R) (H' : Matrix C' Q' R)
    (U : Matrix Q' Q R) (Uinv : Matrix Q Q' R) (P : Matrix C' C R)
    (hU : U * Uinv = 1) (square : H' * U = P * H) :
    dagger H' = dagger Uinv * dagger H * dagger P := by
  have h : H' = P * H * Uinv := by
    rw [← square, Matrix.mul_assoc, hU, Matrix.mul_one]
  rw [h, dagger_mul, dagger_mul, Matrix.mul_assoc]

omit [DecidableEq Q] [DecidableEq C'] in
/-- Second identity in the stabilized check square; the X action is (U⁻¹)†. -/
theorem x_image_certificate
    (H : Matrix C Q R) (H' : Matrix C' Q' R)
    (U : Matrix Q' Q R) (Uinv : Matrix Q Q' R)
    (P : Matrix C' C R) (Pinv : Matrix C C' R)
    (hU : U * Uinv = 1) (hP : Pinv * P = 1)
    (square : H' * U = P * H) (v : Q' → R) :
    (∃ z, dagger Uinv *ᵥ (dagger H *ᵥ z) = v) ↔ inImage (dagger H') v := by
  have hdag := dagger_check_identity H H' U Uinv P hU square
  have hdagP : dagger P * dagger Pinv = 1 := by
    rw [← dagger_mul, hP, dagger_one]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨dagger Pinv *ᵥ z, ?_⟩
    rw [hdag]
    simp only [← mulVec_mulVec]
    rw [mulVec_mulVec z (dagger P) (dagger Pinv), hdagP, one_mulVec]
  · rintro ⟨z, hz⟩
    refine ⟨dagger P *ᵥ z, ?_⟩
    rw [hdag] at hz
    simpa only [mulVec_mulVec, Matrix.mul_assoc] using hz

end
end Decoupling.HighDim.PhysicalIsomorphism

namespace Decoupling.HighDim.PhysicalIsomorphism

noncomputable section
open Matrix

variable {K : Type*} [CommRing K] {D : ℕ}
local notation "R" => Laurent K D

section Locality

variable {ι : Type*} [DecidableEq ι]

/-- Explicit finite depth, bounded physical site distances, disjoint pairs,
and translation covariance of both actual Pauli-label actions in every layer. -/
def LocalCircuit (gates : List (Circuit.Layer K D ι)) : Prop :=
  ∃ depth range : ℕ, depth = gates.length ∧ ∀ g ∈ gates,
    (∀ n, g.source n ≠ g.destination n) ∧
    (∀ n m, n ≠ m → g.source n ≠ g.source m ∧ g.source n ≠ g.destination m ∧
      g.destination n ≠ g.source m ∧ g.destination n ≠ g.destination m) ∧
    (∀ n i, (((g.destination n).2 - (g.source n).2) i).natAbs ≤ range) ∧
    (∀ b f, g.xConfig (Circuit.SUM.translateConfig b f) =
      Circuit.SUM.translateConfig b (g.xConfig f)) ∧
    (∀ b f, g.zConfig (Circuit.SUM.translateConfig b f) =
      Circuit.SUM.translateConfig b (g.zConfig f))

/-- A finite word in the actual layer type has all these locality properties;
none are an additional certificate supplied to the decoupling theorem. -/
theorem localCircuit (gates : List (Circuit.Layer K D ι)) : LocalCircuit gates := by
  refine ⟨gates.length, Circuit.wordRangeBound gates, rfl, ?_⟩
  intro g hg
  exact ⟨g.distinct_sites, fun n m h => g.disjoint_gates h,
    fun n i => Circuit.site_distance_le_wordRangeBound gates g hg n i,
    g.x_translation_covariant, g.z_translation_covariant⟩

end Locality

section Transport

variable {Q Q' C C' Z Z' : Type*}
  [Fintype Q] [Fintype Q'] [Fintype C] [Fintype C'] [Fintype Z] [Fintype Z']
  [DecidableEq Q] [DecidableEq Q']

/-- Both literal stabilizer-module image equalities, in one common physical
species order. The source coordinates are relabeled by the explicit bijection `e`. -/
def Transports (gates : List (Circuit.Layer K D Q')) (e : Q ≃ Q')
    (HC : Matrix C Q R) (HT : Matrix C' Q' R)
    (BC : Matrix Q Z R) (BT : Matrix Q' Z' R) : Prop :=
  (∀ v, (∃ z, Circuit.wordZ gates *ᵥ ((BC *ᵥ z) ∘ e.symm) = v) ↔ inImage BT v) ∧
  (∀ v, (∃ z, Circuit.wordX gates *ᵥ ((dagger HC *ᵥ z) ∘ e.symm) = v) ↔
    inImage (dagger HT) v)

omit [Fintype Q] [DecidableEq Q] in
/-- Fourier conjugation exchanges the two stabilizer sectors while keeping
the circuit a finite word in SUM and SWAP. The gate weights in `fourierDual`
already carry the required odd-characteristic minus signs. -/
theorem transports_fourierDual
    (gates : List (Circuit.Layer K D Q')) (e : Q ≃ Q')
    (HC : Matrix C Q R) (HT : Matrix C' Q' R)
    (BC : Matrix Q Z R) (BT : Matrix Q' Z' R)
    (h : Transports gates e HC HT BC BT) :
    Transports (gates.map Circuit.fourierDual) e
      (dagger BC) (dagger BT) (dagger HC) (dagger HT) := by
  simpa only [Transports, Circuit.wordZ_fourierDual, Circuit.wordX_fourierDual,
    dagger_dagger] using And.intro h.2 h.1

omit [DecidableEq Q] [DecidableEq Q'] in
theorem reindexed_mulVec (U : Matrix Q' Q R) (e : Q ≃ Q') (v : Q → R) :
    U.submatrix id e.symm *ᵥ (v ∘ e.symm) = U *ᵥ v := by
  rw [Matrix.submatrix_mulVec_equiv]
  simp [Function.comp_def]

variable [DecidableEq C] [DecidableEq C']

omit [DecidableEq Q] [DecidableEq C'] in
theorem transports_of_actions
    (gates : List (Circuit.Layer K D Q')) (e : Q ≃ Q')
    (HC : Matrix C Q R) (HT : Matrix C' Q' R)
    (BC : Matrix Q Z R) (BT : Matrix Q' Z' R)
    (U : Matrix Q' Q R) (Uinv : Matrix Q Q' R)
    (V : Matrix C' C R) (Vinv : Matrix C C' R)
    (hU : U * Uinv = 1) (hV : Vinv * V = 1)
    (square : HT * U = V * HC)
    (exactC : ∀ v, HC *ᵥ v = 0 ↔ inImage BC v)
    (exactT : ∀ v, HT *ᵥ v = 0 ↔ inImage BT v)
    (hZ : Circuit.wordZ gates = U.submatrix id e.symm)
    (hX : Circuit.wordX gates = dagger (Uinv.submatrix e.symm id)) :
    Transports gates e HC HT BC BT := by
  constructor
  · intro v
    simp only [hZ, reindexed_mulVec]
    exact z_image_certificate HC HT BC BT U Uinv V Vinv hU hV square exactC exactT v
  · intro v
    have hd : dagger (Uinv.submatrix e.symm id) = (dagger Uinv).submatrix id e.symm := rfl
    simp only [hX, hd, reindexed_mulVec]
    exact x_image_certificate HC HT U Uinv V Vinv hU hV square v

end Transport

section Existence

variable {C₀ C₁ C₂ T₀ T₁ T₂ : Type*}
  [Fintype C₀] [Fintype C₁] [Fintype C₂]
  [Fintype T₀] [Fintype T₁] [Fintype T₂]
  [DecidableEq C₀] [DecidableEq C₁] [DecidableEq T₀] [DecidableEq T₁]

/-- Actual cokernel isomorphism implies a finite local SUM/SWAP circuit after
the displayed |+⟩ and |0⟩ ancillary blocks. Comparison data and circuit words
are constructed, not supplied. No nonempty-index assumption is used. -/
theorem exists_circuit_of_checkEquiv
    (dC : Matrix C₁ C₀ R) (dT : Matrix T₁ T₀ R)
    (zC : Matrix C₀ C₂ R) (zT : Matrix T₀ T₂ R)
    (exactC : ∀ v, dC *ᵥ v = 0 ↔ inImage zC v)
    (exactT : ∀ v, dT *ᵥ v = 0 ↔ inImage zT v)
    (beta : Comparison.CheckCokernel dT ≃ₗ[R] Comparison.CheckCokernel dC)
    (e : ((C₀ ⊕ T₁) ⊕ (T₀ ⊕ C₁)) ≃ ((T₀ ⊕ C₁) ⊕ (C₀ ⊕ T₁))) :
    ∃ gates : List (Circuit.Layer K D ((T₀ ⊕ C₁) ⊕ (C₀ ⊕ T₁))),
      Transports gates e
        (StableCSS.H_X (A := T₁) (B := T₀ ⊕ C₁) dC)
        (StableCSS.H_X (A := C₁) (B := C₀ ⊕ T₁) dT)
        (StableCSS.H_Z_dagger (A := T₁) (B := T₀ ⊕ C₁) zC)
        (StableCSS.H_Z_dagger (A := C₁) (B := C₀ ⊕ T₁) zT) ∧
      ∃ depth range : ℕ, depth = gates.length ∧
        ∀ gate ∈ gates, ∀ i : Fin D, (gate.displacement i).natAbs ≤ range := by
  obtain ⟨c, hdC, hdT, _, _⟩ := Comparison.exists_comparisonData dC dT beta
  obtain ⟨gates, hZ, hX, hfinite⟩ := Circuit.theta_circuit c.psiHat c.phiHat e
  have hc : c.dCHat = StableCSS.H_X (A := T₁) (B := T₀ ⊕ C₁) dC := by
    simp [Stabilization.ComparisonData.dCHat, Stabilization.ComparisonData.dCPrime,
      StableCSS.H_X, hdC]
  have ht : c.dTHat = StableCSS.H_X (A := C₁) (B := C₀ ⊕ T₁) dT := by
    simp [Stabilization.ComparisonData.dTHat, Stabilization.ComparisonData.dTPrime,
      StableCSS.H_X, hdT]
  refine ⟨gates, ?_, hfinite⟩
  apply transports_of_actions gates e _ _ _ _ c.U c.UInv c.V c.VInv
    c.U_inverse.1 c.V_inverse.2
  · simpa only [hc, ht] using c.stabilized_square
  · exact StableCSS.exactness dC zC exactC
  · exact StableCSS.exactness dT zT exactT
  · exact hZ
  · exact hX

end Existence

section StableExistence

variable {C₀ C₁ C₂ T₀ T₁ T₂ A B : Type*}
  [Fintype C₀] [Fintype C₁] [Fintype C₂]
  [Fintype T₀] [Fintype T₁] [Fintype T₂] [Fintype A] [Fintype B]
  [DecidableEq C₀] [DecidableEq C₁] [DecidableEq T₀] [DecidableEq T₁]
  [DecidableEq A] [DecidableEq B]

/-- Absorb an actual stable check-cokernel isomorphism by identity checks,
then construct the comparison maps, stabilization, and finite SUM/SWAP circuit.
The inputs contain no comparison identities or circuit witnesses. -/
theorem exists_circuit_of_stableCheckEquiv
    (dC : Matrix C₁ C₀ R) (dT : Matrix T₁ T₀ R)
    (zC : Matrix C₀ C₂ R) (zT : Matrix T₀ T₂ R)
    (exactC : ∀ v, dC *ᵥ v = 0 ↔ inImage zC v)
    (exactT : ∀ v, dT *ᵥ v = 0 ↔ inImage zT v)
    (beta : (Comparison.CheckCokernel dT × (B → R)) ≃ₗ[R]
      (Comparison.CheckCokernel dC × (A → R)))
    (e : ((C₀ ⊕ (T₁ ⊕ B)) ⊕ (T₀ ⊕ (C₁ ⊕ A))) ≃
      ((T₀ ⊕ (C₁ ⊕ A)) ⊕ (C₀ ⊕ (T₁ ⊕ B)))) :
    ∃ gates : List (Circuit.Layer K D ((T₀ ⊕ (C₁ ⊕ A)) ⊕ (C₀ ⊕ (T₁ ⊕ B)))),
      Transports gates e
        (StableCSS.H_X (A := T₁ ⊕ B) (B := T₀ ⊕ (C₁ ⊕ A))
          (StableCSS.identityChecks (A := A) dC))
        (StableCSS.H_X (A := C₁ ⊕ A) (B := C₀ ⊕ (T₁ ⊕ B))
          (StableCSS.identityChecks (A := B) dT))
        (StableCSS.H_Z_dagger (A := T₁ ⊕ B) (B := T₀ ⊕ (C₁ ⊕ A)) zC)
        (StableCSS.H_Z_dagger (A := C₁ ⊕ A) (B := C₀ ⊕ (T₁ ⊕ B)) zT) ∧
      ∃ depth range : ℕ, depth = gates.length ∧
        ∀ gate ∈ gates, ∀ i : Fin D, (gate.displacement i).natAbs ≤ range := by
  let beta' := (StableCSS.identityCheckCokernelEquiv (A := B) dT).trans
    (beta.trans (StableCSS.identityCheckCokernelEquiv (A := A) dC).symm)
  apply exists_circuit_of_checkEquiv _ _ zC zT _ _ beta' e
  · intro v
    exact (StableCSS.identityChecks_kernel dC v).trans (exactC v)
  · intro v
    exact (StableCSS.identityChecks_kernel dT v).trans (exactT v)

end StableExistence

section CSS

variable {q s r q' s' r' a b : ℕ}

/-- The conditional physical conclusion for actual topological CSS data.
Only their actual stable check-cokernel equivalence is an additional input;
its derivation from the profiles is an upstream theorem. This conclusion
constructs a finite SUM/SWAP word on the original lattice, with finite range.
The two `Transports` clauses are the Z- and X-stabilizer module equalities. -/
theorem exists_css_circuit_of_stableCheckEquiv
    (c : CSS.Checks K D q s r) (hc : c.Topological)
    (t : CSS.Checks K D q' s' r') (ht : t.Topological)
    (beta : (t.CheckCokernel × (Fin b → R)) ≃ₗ[R]
      (c.CheckCokernel × (Fin a → R))) :
    ∃ gates : List (Circuit.Layer K D
        ((Fin q' ⊕ (Fin s ⊕ Fin a)) ⊕ (Fin q ⊕ (Fin s' ⊕ Fin b)))),
      Transports gates (Equiv.sumComm _ _)
        (StableCSS.H_X (A := Fin s' ⊕ Fin b) (B := Fin q' ⊕ (Fin s ⊕ Fin a))
          (StableCSS.identityChecks (A := Fin a) c.H_X))
        (StableCSS.H_X (A := Fin s ⊕ Fin a) (B := Fin q ⊕ (Fin s' ⊕ Fin b))
          (StableCSS.identityChecks (A := Fin b) t.H_X))
        (StableCSS.H_Z_dagger (A := Fin s' ⊕ Fin b) (B := Fin q' ⊕ (Fin s ⊕ Fin a))
          (dagger c.H_Z))
        (StableCSS.H_Z_dagger (A := Fin s ⊕ Fin a) (B := Fin q ⊕ (Fin s' ⊕ Fin b))
          (dagger t.H_Z)) ∧
      ∃ depth range : ℕ, depth = gates.length ∧
        ∀ gate ∈ gates, ∀ i : Fin D, (gate.displacement i).natAbs ≤ range :=
  exists_circuit_of_stableCheckEquiv c.H_X t.H_X (dagger c.H_Z) (dagger t.H_Z)
    (c.exact_X hc) (t.exact_X ht) beta (Equiv.sumComm _ _)

/-- The same conditional result from the Z-side check cokernels. Applying
the preceding theorem to the exchanged sectors and conjugating each local
gate by Fourier stays within SUM/SWAP. The displayed ancillary checks are
the duals of the exchanged construction, so |0⟩ and |+⟩ trade roles. -/
theorem exists_css_circuit_of_stableCheckEquiv_Z
    (c : CSS.Checks K D q s r) (hc : c.Topological)
    (t : CSS.Checks K D q' s' r') (ht : t.Topological)
    (beta : (t.swap.CheckCokernel × (Fin b → R)) ≃ₗ[R]
      (c.swap.CheckCokernel × (Fin a → R))) :
    ∃ gates : List (Circuit.Layer K D
        ((Fin q' ⊕ (Fin r ⊕ Fin a)) ⊕ (Fin q ⊕ (Fin r' ⊕ Fin b)))),
      Transports gates (Equiv.sumComm _ _)
        (dagger (StableCSS.H_Z_dagger (A := Fin r' ⊕ Fin b)
          (B := Fin q' ⊕ (Fin r ⊕ Fin a)) (dagger c.H_X)))
        (dagger (StableCSS.H_Z_dagger (A := Fin r ⊕ Fin a)
          (B := Fin q ⊕ (Fin r' ⊕ Fin b)) (dagger t.H_X)))
        (dagger (StableCSS.H_X (A := Fin r' ⊕ Fin b)
          (B := Fin q' ⊕ (Fin r ⊕ Fin a)) (StableCSS.identityChecks (A := Fin a) c.H_Z)))
        (dagger (StableCSS.H_X (A := Fin r ⊕ Fin a)
          (B := Fin q ⊕ (Fin r' ⊕ Fin b)) (StableCSS.identityChecks (A := Fin b) t.H_Z))) ∧
      ∃ depth range : ℕ, depth = gates.length ∧
        ∀ gate ∈ gates, ∀ i : Fin D, (gate.displacement i).natAbs ≤ range := by
  obtain ⟨gates, htransport, _⟩ := exists_css_circuit_of_stableCheckEquiv
    c.swap (c.topological_swap hc) t.swap (t.topological_swap ht) beta
  exact ⟨gates.map Circuit.fourierDual,
    transports_fourierDual gates _ _ _ _ _ htransport, Circuit.word_finite_depth_range _⟩

end CSS

end
end Decoupling.HighDim.PhysicalIsomorphism
