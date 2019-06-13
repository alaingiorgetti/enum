type ('a, 'b) map = 'a -> 'b

let get : type a b. (a -> b) -> a ->  b = fun f x -> f x

let mixfix_lbrb : type a b. (a -> b) -> a ->  b = fun f x -> f x

