let rec split3 = function
  | [] -> [], [], []
  | (a,b,c)::l -> let l1, l2, l3 = split3 l in a::l1, b::l2, c::l3

let rec is_prefix s1 s2 = (* returns true if s1 is a prefix of s2 *)
  let l1 = String.length s1 in
  let l2 = String.length s2 in
  if l1 = 0 then true
  else if l2 = 0 then false
  else s1.[0] = s2.[0]
    && (is_prefix (String.sub s1 1 (l1-1)) (String.sub s2 1 (l2-1)))
