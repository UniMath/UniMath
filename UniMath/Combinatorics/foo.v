Variable m n : nat.
Notation "C ⟦ m , n ⟧" := (m + n) (at level 50).
Notation "⟦ n ⟧" := (2 * n) (at level 50) : stn.
Delimit Scope stn with stn.
Open Scope stn.
Definition foo := ⟦n⟧ % stn.
Definition bar := C⟦m,n⟧.
Print foo.
Print bar.
