
let record_delete x = ((x\l1)\l2)\l3
let record_update x = { x with l1 = 1 ; l2=2 ; l3=3 }

let record_delete_ann (x:{ ;; 'a}) = ((x\l1)\l2)\l3
let record_update_ann (x:{ ;; 'a}) = { x with l1 = 1 ; l2=2 ; l3=3 }

let record_test =
  let r1 = {l3=33 ; l4=44} in
  let r2 = record_update r1 in
  let r3 = record_delete r2 in
  (r1,r2,r3)


val extract_ellipsis_param1 : { l1: any? ;; 'a? } -> 'a
val extract_ellipsis_param2 : { l1: any? ; l2: any? ;; 'a? } -> 'a
val extract_ellipsis_param3 : { l1: any? ; l2: any? ; l3: any? ;; 'a? } -> 'a
let extract_ellipsis_test =
  let params = {l1=42 ; l2=73 ; l3=false ; l4=true} in
  extract_ellipsis_param1 params, extract_ellipsis_param2 params, extract_ellipsis_param3 params
