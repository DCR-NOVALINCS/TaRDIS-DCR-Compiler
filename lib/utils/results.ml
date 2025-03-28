let ( >>= ) = Result.bind

let fold_left_error f acc l =
  let rec fold_helper acc = function
    | [] -> Ok acc
    | x :: xs -> f acc x >>= fun acc' -> fold_helper acc' xs
  in
  fold_helper acc l

let iter_left_error f l =
  let rec iter_helper = function
    | [] -> Ok ()
    | x :: xs -> f x >>= fun () -> iter_helper xs
  in
  iter_helper l
