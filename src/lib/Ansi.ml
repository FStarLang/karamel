let mkcolor x = Printf.sprintf "\x1b[38;5;%dm" x

let green = mkcolor 119
let red = mkcolor 203
let blue = mkcolor 81
let yellow = mkcolor 227
let orange = mkcolor 202
let underline = "\x1b[4m"
let reset = "\x1b[0m"
