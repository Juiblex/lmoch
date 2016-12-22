let rec split3 = function
  | [] -> [], [], []
  | (a,b,c)::l -> let l1, l2, l3 = split3 l in a::l1, b::l2, c::l3
