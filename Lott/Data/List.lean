theorem List.map_singleton_join (xs : List α) : (xs.map fun x => [f x]).join = xs.map f :=
  match xs with
  | [] => rfl
  | x :: xs' => by rw [List.map, List.map, List.join, List.singleton_append, xs'.map_singleton_join]
