
val compare : (int,int) | (bool,bool) | (string,string) | (char,char) -> int
val (=) : (int,int) | (bool,bool) | (string,string) | (char,char) -> bool

#infer_overload = false
#type_narrowing = false

let f_nopoly x =
  match x with
  | 0 -> 0 | 1 -> 1 | 2 -> 2 | 3 -> 3 | 4 -> 4
  | 5 -> 5 | 6 -> 6 | 7 -> 7 | 8 -> 8 | 9 -> 9
  | 10 -> 10 | 11 -> 11 | 12 -> 12 | 13 -> 13 | 14 -> 14
  | 15 -> 15 | 16 -> 16 | 17 -> 17 | 18 -> 18 | 19 -> 19
  | 20 -> 20 | 21 -> 21 | 22 -> 22 | 23 -> 23 | 24 -> 24
  | _ -> (-1)
  end

let test_nopoly (y:(10..15)) = f_nopoly y

#infer_overload = true

let f x =
  match x with
  | 0 -> 0 | 1 -> 1 | 2 -> 2 | 3 -> 3 | 4 -> 4
  | 5 -> 5 | 6 -> 6 | 7 -> 7 | 8 -> 8 | 9 -> 9
  | 10 -> 10 | 11 -> 11 | 12 -> 12 | 13 -> 13 | 14 -> 14
  | 15 -> 15 | 16 -> 16 | 17 -> 17 | 18 -> 18 | 19 -> 19
  | 20 -> 20 | 21 -> 21 | 22 -> 22 | 23 -> 23 | 24 -> 24
  | _ -> (-1)
  end

let test (y:(10..15)) = f y

#infer_overload = true
#type_narrowing = true
