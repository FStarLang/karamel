module ForwardDecl

module B = LowStar.Buffer

#push-options "--__no_positivity"
unopteq type a = {
 x : b;
} and b = {
 y : B.pointer a;
}
#pop-options

let main () = 0l
