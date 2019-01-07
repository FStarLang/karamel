module ForwardDecl

module B = LowStar.Buffer

unopteq type a = {
 x : b;
} and b = {
 y : B.pointer a;
}

let main () = 0l
