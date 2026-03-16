module Base
type test = | Foo | Bar

let f (x: Base.test) : Tot bool = Base.Foo? x
