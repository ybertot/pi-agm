Require Import BigZ rounding_big String.

(*
Eval native_compute in let m := (10 ^ 1200)%bigZ in 
  (salamin m 10 - hpi m 10)%bigZ.

Time Eval native_compute in let m := (10 ^ 1200)%bigZ in
  let v := salamin m 10 in 
  ("computed salamin (10 ^ 1200) 10"%string, (v =? 0)%bigZ).


Time Eval native_compute in let m := (10 ^ 1200)%bigZ in
  let v := hpi m 10 in
  ("computed hpi (10 ^ 1200) 10"%string, (v =? 0)%bigZ).

Time Eval native_compute in let m := (10 ^ 10200)%bigZ in
  let v := salamin m 10 in 
  ("computed salamin (10 ^ 10200) 10"%string, (v =? 0)%bigZ).


Time Eval native_compute in let m := (10 ^ 10200)%bigZ in
  let v := hpi m 10 in
  ("computed hpi (10 ^ 10200) 10"%string, (v =? 0)%bigZ).

Eval native_compute in let m := (10 ^ 10200)%bigZ in let i := 13 in
  ("comparison at 10200 digits, 13 iterations"%string,
   (salamin m i - hpi m i)%bigZ).

Eval native_compute in let m := (10 ^ 10200)%bigZ in let i := 14 in
  ("comparison at 10200 digits, 14 iterations"%string,
   (salamin m i - hpi m i)%bigZ).

Time Eval native_compute in let m := (10 ^ 11000)%bigZ in let i := 14 in
  ("comparison at 10200 digits, 13 salamin, 14 iterations hpi"%string,
   (salamin m 13 - hpi m i)%bigZ).
*)

Time Eval native_compute in let m := (2 ^ 3321959)%bigZ in
  let n := salamin m 20 in
  let n' := (n * 10 ^ (10 ^ 6 + 7) / m)%bigZ in
  let (q, r) := BigZ.div_eucl n' (10 ^ 7) in
  q.
  