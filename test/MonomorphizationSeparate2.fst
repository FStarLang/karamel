module MonomorphizationSeparate2

let fst (x: MonomorphizationSeparate1.pair) = fst x

let main () = fst MonomorphizationSeparate1.(foo, foo)
