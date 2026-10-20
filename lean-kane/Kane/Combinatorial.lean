import Kane.Cube

/-! The edge-charging argument for a union of unate Boolean functions. -/

open scoped BigOperators

namespace Kane

def newPart {n : ℕ} (f g : Cube n → Bool) (x : Cube n) : ℝ :=
  boolVal (f x && !(g x))

lemma newPart_eq_sub {n : ℕ} (f g : Cube n → Bool) (x : Cube n) :
    newPart f g x = boolVal (f x || g x) - boolVal (g x) := by
  cases hf : f x <;> cases hg : g x <;> simp [newPart, boolVal, hf, hg]

private lemma bool_edge_bound (a b u v c : Bool)
    (h : if c then b ≤ a else a ≤ b) :
    (if (a || u) = (b || v) then (0 : ℝ) else 1) -
        (if u = v then (0 : ℝ) else 1) ≤
      (if c then (1 : ℝ) else -1) *
        ((boolVal (a || u) - boolVal u) - (boolVal (b || v) - boolVal v)) := by
  cases a <;> cases b <;> cases u <;> cases v <;> cases c <;>
    norm_num [boolVal, Bool.le_iff_imp] at *

lemma unate_edge_bound {n : ℕ} (f : UnateFunction n) (g : Cube n → Bool)
    (x : Cube n) (i : Fin n) :
    (if (f.fn x || g x) = (f.fn (flip x i) || g (flip x i)) then (0 : ℝ) else 1) -
        (if g x = g (flip x i) then (0 : ℝ) else 1) ≤
      signedCoord f.direction x i *
        (newPart f.fn g x - newPart f.fn g (flip x i)) := by
  rw [newPart_eq_sub, newPart_eq_sub]
  by_cases hx : x i = f.direction i
  · simpa [signedCoord, hx] using
      bool_edge_bound (f.fn x) (f.fn (flip x i)) (g x) (g (flip x i)) true
        (by simpa using f.increasing x i hx)
  · have hflip : (flip x i) i = f.direction i := by
      simp only [flip, Function.update_self]
      cases hxi : x i <;> cases hsi : f.direction i <;> simp_all
    have hmono : f.fn x ≤ f.fn (flip x i) := by
      simpa using f.increasing (flip x i) i hflip
    simpa [signedCoord, hx] using
      bool_edge_bound (f.fn x) (f.fn (flip x i)) (g x) (g (flip x i)) false
        (by simpa using hmono)

lemma avg_signed_difference {n : ℕ} (s : Cube n) (S : Cube n → ℝ) :
    avg (fun x => ∑ i : Fin n, signedCoord s x i * (S x - S (flip x i))) =
      2 * avg (fun x => S x * signedSum s x) := by
  have hcoord (i : Fin n) :
      avg (fun x => signedCoord s x i * (S x - S (flip x i))) =
        2 * avg (fun x => S x * signedCoord s x i) := by
    have hflip : avg (fun x => signedCoord s x i * S (flip x i)) =
        -avg (fun x => signedCoord s x i * S x) := by
      calc
        _ = avg (fun x => signedCoord s (flip x i) i * S (flip (flip x i) i)) :=
          (avg_flip (fun x => signedCoord s x i * S (flip x i)) i).symm
        _ = avg (fun x => (-1 : ℝ) * (signedCoord s x i * S x)) := by
          congr 1
          funext x
          simp [signedCoord_flip_self]
        _ = -avg (fun x => signedCoord s x i * S x) := by
          rw [avg_const_mul]
          ring
    calc
      _ = avg (fun x => signedCoord s x i * S x) -
          avg (fun x => signedCoord s x i * S (flip x i)) := by
        rw [← avg_sub]
        congr 1
        funext x
        ring
      _ = 2 * avg (fun x => S x * signedCoord s x i) := by
        rw [hflip]
        have hm : avg (fun x => signedCoord s x i * S x) =
            avg (fun x => S x * signedCoord s x i) :=
          avg_congr (fun x => mul_comm _ _)
        rw [hm]
        ring
  rw [avg_sum]
  simp_rw [hcoord]
  rw [← Finset.mul_sum, ← avg_sum]
  congr 1
  congr 1
  funext x
  simp [signedSum, Finset.mul_sum]

theorem averageSensitivity_or_le {n : ℕ} (f : UnateFunction n)
    (g : Cube n → Bool) :
    averageSensitivity (fun x => f.fn x || g x) ≤
      averageSensitivity g + 2 * avg (fun x => newPart f.fn g x * signedSum f.direction x) := by
  have h : averageSensitivity (fun x => f.fn x || g x) - averageSensitivity g ≤
      2 * avg (fun x => newPart f.fn g x * signedSum f.direction x) := by
    calc
      _ = avg (fun x => ∑ i : Fin n,
          ((if (f.fn x || g x) = (f.fn (flip x i) || g (flip x i)) then (0 : ℝ) else 1) -
            (if g x = g (flip x i) then (0 : ℝ) else 1))) := by
        simp only [averageSensitivity, ← avg_sub, Finset.sum_sub_distrib]
      _ ≤ avg (fun x => ∑ i : Fin n, signedCoord f.direction x i *
          (newPart f.fn g x - newPart f.fn g (flip x i))) := by
        apply avg_mono
        intro x
        exact Finset.sum_le_sum fun i _ => unate_edge_bound f g x i
      _ = _ := avg_signed_difference f.direction (newPart f.fn g)
  linarith

private theorem union_charge_aux {n : ℕ} (fs : List (UnateFunction n)) :
    ∃ G : Cube n → ℝ,
      averageSensitivity (union fs) ≤ 2 * avg G ∧
      (∀ x, G x = 0 ∨ ∃ f ∈ fs, G x = signedSum f.direction x) ∧
      (∀ x, union fs x = false → G x = 0) := by
  induction fs with
  | nil =>
      refine ⟨fun _ => 0, ?_, ?_, ?_⟩
      · simp [averageSensitivity, union, avg]
      · exact fun _ => Or.inl rfl
      · exact fun _ _ => rfl
  | cons f fs ih =>
      obtain ⟨G, hbound, hselect, hzero⟩ := ih
      let H : Cube n → ℝ := fun x => G x + newPart f.fn (union fs) x * signedSum f.direction x
      refine ⟨H, ?_, ?_, ?_⟩
      · have hstep := averageSensitivity_or_le f (union fs)
        have havg : avg H = avg G +
            avg (fun x => newPart f.fn (union fs) x * signedSum f.direction x) :=
          avg_add _ _
        change averageSensitivity (fun x => f.fn x || union fs x) ≤ _
        rw [havg]
        linarith
      · intro x
        cases hg : union fs x with
        | false =>
            have hz := hzero x hg
            cases hf : f.fn x with
            | false => exact Or.inl (by simp [H, newPart, boolVal, hg, hf, hz])
            | true =>
                exact Or.inr ⟨f, by simp, by simp [H, newPart, boolVal, hg, hf, hz]⟩
        | true =>
            have hh : H x = G x := by simp [H, newPart, boolVal, hg]
            rw [hh]
            rcases hselect x with hz | ⟨g, hgmem, heq⟩
            · exact Or.inl hz
            · exact Or.inr ⟨g, List.mem_cons_of_mem _ hgmem, heq⟩
      · intro x hx
        have hg : union fs x = false := by
          cases hg : union fs x <;> simp_all [union]
        have hf : f.fn x = false := by
          cases hf : f.fn x <;> simp_all [union]
        simp [H, newPart, boolVal, hg, hf, hzero x hg]

/-- A union's sensitivity is charged to at most one signed coordinate sum at each point. -/
theorem union_sensitivity_charge {n : ℕ} (fs : List (UnateFunction n)) :
    ∃ G : Cube n → ℝ,
      averageSensitivity (union fs) ≤ 2 * avg G ∧
      ∀ x, G x = 0 ∨ ∃ f ∈ fs, G x = signedSum f.direction x := by
  obtain ⟨G, hb, hs, _⟩ := union_charge_aux fs
  exact ⟨G, hb, hs⟩

end Kane
